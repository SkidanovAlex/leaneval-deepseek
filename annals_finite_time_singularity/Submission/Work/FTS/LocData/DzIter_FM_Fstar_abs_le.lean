/-
# `Work.FTS.LocData.DzIter_FM_Fstar_abs_le`

The first four iterates of `D_z = z ∂_z` applied to the fundamental-model profile
`F_* (z) = 2z/(1+z)²` (`Work.FM.Fstar`) decay like `1/z` at infinity:

`|D_z^j F_* (z)| ≤ C/z` for `z ≥ 1`, `j ≤ 4`.

This is the `z`-part of the `ℋ⁴`-estimate of the localised data: the angular weight
`w = (1+z)²/z²` of `Work.Spaces` blows up like `z²` at `z = ∞` while the *bare* `D_z`-iterates
of `F_*` decay like `1/z`, which is what makes the far part `zfar L F_*` of the profile
integrable against the weight.

## The argument

* The `θ`-variable is a dummy in `fun z _ => F_* z`, so
  `DzIter j (fun z _ => F_* z) z θ = (T1F^[j]) F_* z`, where `T1F u z = z ∂_z u z`
  (`DzIter_Fstar_eq_T1`).

* The plain derivatives of `F_*` have the closed form
  `deriv^[k] F_* z = Gker k z = 2·(-1)^k·k!·(z-k)/(1+z)^(k+2)`
  (`Submission.Work.FTS.LocData.hasDerivAt_Gker` gives `deriv (Gker k) = Gker (k+1)` off
  `z = -1`).

* Expanding `T1F^[j]` for `j ≤ 4` in terms of `deriv^[k] F_*` (`T1_iter_Fstar_*` below) and
  bounding each term by `10·k!/z` for `z ≥ 1`
  (`Submission.Work.FTS.LocData.abs_zpow_mul_Gker_le`) gives the estimate with `C = 1000`.

## Traps

`T1F` is `z ∂_z`, not `∂_z`; the factors `z^k` produced by the iteration have to be carried
along, which is why the expansion coefficients are the Stirling numbers `1, 1, 3, 1, 7, 6, 1`
and not binomial coefficients.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.FstarAux
import Submission.Work.FTS.LocData.hasDerivAt_Gker
import Submission.Work.FTS.LocData.abs_zpow_mul_Gker_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## `D_z^j` of the profile as an iterate of the one-variable operator `T1F` -/

/-- The `θ`-variable is a dummy in `fun z _ => F_* z`, so the iterated `D_z` on the profile is
the iterate of the one-variable operator `T1F u z = z ∂_z u z`. -/
theorem DzIter_Fstar_eq_T1 (j : ℕ) (θ z : ℝ) :
    Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ = (T1F^[j]) Work.FM.Fstar z := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Function.iterate_succ_apply']
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z' θ)
          = (T1F^[j]) Work.FM.Fstar := funext fun z' => ih z'
      show z * deriv (fun z' : ℝ => Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z' θ) z
          = T1F ((T1F^[j]) Work.FM.Fstar) z
      rw [hfun]
      rfl

/-! ## The closed forms of the iterated derivatives -/

/-- `deriv (Gker k) z = Gker (k+1) z` for `z > 1/2` (where `1 + z ≠ 0`). -/
theorem deriv_Gker_eq (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (1 / 2)) :
    deriv (Gker k) z = Gker (k + 1) z := by
  have hlt : (1 : ℝ) / 2 < z := hz
  exact (hasDerivAt_Gker k z (by linarith)).deriv

/-- The `z`-derivative of `z^k · Gker k` as a `HasDerivAt`: the product rule with the recursion
`deriv (Gker k) = Gker (k+1)`. -/
theorem hasDerivAt_zpow_mul_Gker (j k : ℕ) {z : ℝ} (hz : 1 + z ≠ 0) :
    HasDerivAt (fun w : ℝ => w ^ j * Gker k w)
      ((j : ℝ) * z ^ (j - 1) * Gker k z + z ^ j * Gker (k + 1) z) z := by
  have h := (hasDerivAt_pow j z).mul (hasDerivAt_Gker k z hz)
  have hfun : ((fun x : ℝ => x ^ j) * Gker k) = (fun w : ℝ => w ^ j * Gker k w) := by
    funext w; rfl
  rwa [hfun] at h

/-- `T1F^[0] F_* = F_* = Gker 0`. -/
theorem T1_iter_Fstar_0 :
    Set.EqOn (T1F^[0] Work.FM.Fstar) (Gker 0) (Set.Ioi (1 / 2)) := by
  intro z _
  show Work.FM.Fstar z = Gker 0 z
  rw [Gker_zero]

/-- `T1F^[1] F_* (z) = z·F_*'(z) = z·Gker 1 z`. -/
theorem T1_iter_Fstar_1 :
    Set.EqOn (T1F^[1] Work.FM.Fstar) (fun z => z ^ 1 * Gker 1 z) (Set.Ioi (1 / 2)) := by
  intro z hz
  have hlt : (1 : ℝ) / 2 < z := hz
  have hz0 : 1 + z ≠ 0 := by linarith
  show T1F Work.FM.Fstar z = z ^ 1 * Gker 1 z
  rw [T1_apply]
  have hd : deriv Work.FM.Fstar z = Gker 1 z := by
    rw [show Work.FM.Fstar = Gker 0 from funext fun w => (Gker_zero w).symm]
    exact (hasDerivAt_Gker 0 z hz0).deriv
  rw [hd]
  ring

/-- `T1F^[2] F_* (z) = z·Gker 1 z + z²·Gker 2 z`. -/
theorem T1_iter_Fstar_2 :
    Set.EqOn (T1F^[2] Work.FM.Fstar)
      (fun z => z ^ 1 * Gker 1 z + z ^ 2 * Gker 2 z) (Set.Ioi (1 / 2)) := by
  intro z hz
  have hlt : (1 : ℝ) / 2 < z := hz
  have hz0 : 1 + z ≠ 0 := by linarith
  have hiter : (T1F^[2]) Work.FM.Fstar = T1F ((T1F^[1]) Work.FM.Fstar) := rfl
  rw [hiter, T1_apply]
  have hd1 : deriv ((T1F^[1]) Work.FM.Fstar) z
      = deriv (fun w : ℝ => w ^ 1 * Gker 1 w) z :=
    (T1_iter_Fstar_1.deriv isOpen_Ioi) hz
  rw [hd1]
  have hd : deriv (fun w : ℝ => w ^ 1 * Gker 1 w) z = Gker 1 z + z * Gker 2 z := by
    have h := (hasDerivAt_zpow_mul_Gker 1 1 hz0).deriv
    convert h using 1 <;> (push_cast; ring_nf)
  rw [hd]
  ring

/-- `T1F^[3] F_* (z) = z·Gker 1 z + 3z²·Gker 2 z + z³·Gker 3 z`. -/
theorem T1_iter_Fstar_3 :
    Set.EqOn (T1F^[3] Work.FM.Fstar)
      (fun z => z ^ 1 * Gker 1 z + 3 * (z ^ 2 * Gker 2 z) + z ^ 3 * Gker 3 z)
      (Set.Ioi (1 / 2)) := by
  intro z hz
  have hlt : (1 : ℝ) / 2 < z := hz
  have hz0 : 1 + z ≠ 0 := by linarith
  have hiter : (T1F^[3]) Work.FM.Fstar = T1F ((T1F^[2]) Work.FM.Fstar) := rfl
  rw [hiter, T1_apply]
  have hd1 : deriv ((T1F^[2]) Work.FM.Fstar) z
      = deriv (fun w : ℝ => w ^ 1 * Gker 1 w + w ^ 2 * Gker 2 w) z :=
    (T1_iter_Fstar_2.deriv isOpen_Ioi) hz
  rw [hd1]
  have hd : deriv (fun w : ℝ => w ^ 1 * Gker 1 w + w ^ 2 * Gker 2 w) z
      = Gker 1 z + 3 * z * Gker 2 z + z ^ 2 * Gker 3 z := by
    have h := ((hasDerivAt_zpow_mul_Gker 1 1 hz0).add
      (hasDerivAt_zpow_mul_Gker 2 2 hz0)).deriv
    rw [show ((fun w : ℝ => w ^ 1 * Gker 1 w) + (fun w : ℝ => w ^ 2 * Gker 2 w))
        = (fun w : ℝ => w ^ 1 * Gker 1 w + w ^ 2 * Gker 2 w) from by
      funext w; rfl] at h
    convert h using 1 <;> (push_cast; ring_nf)
  rw [hd]
  ring

/-- `T1F^[4] F_* (z) = z·Gker 1 z + 7z²·Gker 2 z + 6z³·Gker 3 z + z⁴·Gker 4 z`. -/
theorem T1_iter_Fstar_4 :
    Set.EqOn (T1F^[4] Work.FM.Fstar)
      (fun z => z ^ 1 * Gker 1 z + 7 * (z ^ 2 * Gker 2 z) + 6 * (z ^ 3 * Gker 3 z)
        + z ^ 4 * Gker 4 z) (Set.Ioi (1 / 2)) := by
  intro z hz
  have hlt : (1 : ℝ) / 2 < z := hz
  have hz0 : 1 + z ≠ 0 := by linarith
  have hiter : (T1F^[4]) Work.FM.Fstar = T1F ((T1F^[3]) Work.FM.Fstar) := rfl
  rw [hiter, T1_apply]
  have hd1 : deriv ((T1F^[3]) Work.FM.Fstar) z
      = deriv (fun w : ℝ => w ^ 1 * Gker 1 w + 3 * (w ^ 2 * Gker 2 w)
          + w ^ 3 * Gker 3 w) z :=
    (T1_iter_Fstar_3.deriv isOpen_Ioi) hz
  rw [hd1]
  have hd : deriv (fun w : ℝ => w ^ 1 * Gker 1 w + 3 * (w ^ 2 * Gker 2 w)
        + w ^ 3 * Gker 3 w) z
      = Gker 1 z + 7 * z * Gker 2 z + 6 * z ^ 2 * Gker 3 z + z ^ 3 * Gker 4 z := by
    have h := (((hasDerivAt_zpow_mul_Gker 1 1 hz0).add
        ((hasDerivAt_zpow_mul_Gker 2 2 hz0).const_mul 3)).add
      (hasDerivAt_zpow_mul_Gker 3 3 hz0)).deriv
    rw [show (((fun w : ℝ => w ^ 1 * Gker 1 w)
          + (fun w : ℝ => 3 * (w ^ 2 * Gker 2 w)))
          + (fun w : ℝ => w ^ 3 * Gker 3 w))
        = (fun w : ℝ => w ^ 1 * Gker 1 w + 3 * (w ^ 2 * Gker 2 w)
          + w ^ 3 * Gker 3 w) from by
      funext w; rfl] at h
    convert h using 1 <;> (push_cast; ring_nf)
  rw [hd]
  ring

/-! ## The estimate -/

/-- **The first four `D_z`-iterates of the profile decay like `1/z`.** -/
theorem DzIter_FM_Fstar_abs_le :
    ∃ C : ℝ, ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ C / z := by
  refine ⟨1000, ?_⟩
  intro j hj z hz θ
  have hz' : z ∈ Set.Ioi (1 / 2) := by
    rw [Set.mem_Ioi]; linarith
  have hzpos : (0 : ℝ) < z := by linarith
  rw [DzIter_Fstar_eq_T1 j θ z]
  interval_cases j
  · rw [T1_iter_Fstar_0 hz']
    have h1 : |Gker 0 z| ≤ 10 / z := by
      have h := abs_zpow_mul_Gker_le 0 (by norm_num) hz
      rw [show ((0 : ℕ).factorial : ℝ) = 1 by norm_num, pow_zero, one_mul, mul_one] at h
      exact h
    calc |Gker 0 z| ≤ 10 / z := h1
      _ ≤ 1000 / z := div_le_div_of_nonneg_right (by norm_num) hzpos.le
  · rw [T1_iter_Fstar_1 hz']
    have h1 : |z ^ 1 * Gker 1 z| ≤ 10 / z := by
      have h := abs_zpow_mul_Gker_le 1 (by norm_num) hz
      rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num, mul_one] at h
      exact h
    calc |z ^ 1 * Gker 1 z| ≤ 10 / z := h1
      _ ≤ 1000 / z := div_le_div_of_nonneg_right (by norm_num) hzpos.le
  · rw [T1_iter_Fstar_2 hz']
    have h1 : |z ^ 1 * Gker 1 z| ≤ 10 / z := by
      have h := abs_zpow_mul_Gker_le 1 (by norm_num) hz
      rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num, mul_one] at h
      exact h
    have h2 : |z ^ 2 * Gker 2 z| ≤ 20 / z := by
      have h := abs_zpow_mul_Gker_le 2 (by norm_num) hz
      rw [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] at h
      have h20 : (10 : ℝ) * 2 / z = 20 / z := by norm_num
      rwa [h20] at h
    calc |z ^ 1 * Gker 1 z + z ^ 2 * Gker 2 z|
        ≤ |z ^ 1 * Gker 1 z| + |z ^ 2 * Gker 2 z| := abs_add_le _ _
      _ ≤ 10 / z + 20 / z := add_le_add h1 h2
      _ ≤ 1000 / z := by
          rw [show (10 : ℝ) / z + 20 / z = 30 / z by rw [← add_div]; norm_num]
          exact div_le_div_of_nonneg_right (by norm_num) hzpos.le
  · rw [T1_iter_Fstar_3 hz']
    have h1 : |z ^ 1 * Gker 1 z| ≤ 10 / z := by
      have h := abs_zpow_mul_Gker_le 1 (by norm_num) hz
      rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num, mul_one] at h
      exact h
    have h2 : |z ^ 2 * Gker 2 z| ≤ 20 / z := by
      have h := abs_zpow_mul_Gker_le 2 (by norm_num) hz
      rw [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] at h
      have h20 : (10 : ℝ) * 2 / z = 20 / z := by norm_num
      rwa [h20] at h
    have h3 : |z ^ 3 * Gker 3 z| ≤ 60 / z := by
      have h := abs_zpow_mul_Gker_le 3 (by norm_num) hz
      rw [show ((3 : ℕ).factorial : ℝ) = 6 by norm_num] at h
      have h60 : (10 : ℝ) * 6 / z = 60 / z := by norm_num
      rwa [h60] at h
    have hB : |(3 : ℝ) * (z ^ 2 * Gker 2 z)| ≤ 60 / z := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      calc (3 : ℝ) * |z ^ 2 * Gker 2 z| ≤ 3 * (20 / z) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 60 / z := by rw [mul_div_assoc']; norm_num
    calc |z ^ 1 * Gker 1 z + 3 * (z ^ 2 * Gker 2 z) + z ^ 3 * Gker 3 z|
        ≤ |z ^ 1 * Gker 1 z + 3 * (z ^ 2 * Gker 2 z)| + |z ^ 3 * Gker 3 z| := abs_add_le _ _
      _ ≤ (|z ^ 1 * Gker 1 z| + |(3 : ℝ) * (z ^ 2 * Gker 2 z)|) + |z ^ 3 * Gker 3 z| :=
            add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (10 / z + 60 / z) + 60 / z := add_le_add (add_le_add h1 hB) h3
      _ ≤ 1000 / z := by
          rw [show (10 : ℝ) / z + 60 / z + 60 / z = 130 / z by
            rw [← add_div, ← add_div]; norm_num]
          exact div_le_div_of_nonneg_right (by norm_num) hzpos.le
  · rw [T1_iter_Fstar_4 hz']
    have h1 : |z ^ 1 * Gker 1 z| ≤ 10 / z := by
      have h := abs_zpow_mul_Gker_le 1 (by norm_num) hz
      rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num, mul_one] at h
      exact h
    have h2 : |z ^ 2 * Gker 2 z| ≤ 20 / z := by
      have h := abs_zpow_mul_Gker_le 2 (by norm_num) hz
      rw [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] at h
      have h20 : (10 : ℝ) * 2 / z = 20 / z := by norm_num
      rwa [h20] at h
    have h3 : |z ^ 3 * Gker 3 z| ≤ 60 / z := by
      have h := abs_zpow_mul_Gker_le 3 (by norm_num) hz
      rw [show ((3 : ℕ).factorial : ℝ) = 6 by norm_num] at h
      have h60 : (10 : ℝ) * 6 / z = 60 / z := by norm_num
      rwa [h60] at h
    have h4 : |z ^ 4 * Gker 4 z| ≤ 240 / z := by
      have h := abs_zpow_mul_Gker_le 4 (by norm_num) hz
      rw [show ((4 : ℕ).factorial : ℝ) = 24 by norm_num] at h
      have h240 : (10 : ℝ) * 24 / z = 240 / z := by norm_num
      rwa [h240] at h
    have hB : |(7 : ℝ) * (z ^ 2 * Gker 2 z)| ≤ 140 / z := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7)]
      calc (7 : ℝ) * |z ^ 2 * Gker 2 z| ≤ 7 * (20 / z) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 140 / z := by rw [mul_div_assoc']; norm_num
    have hC : |(6 : ℝ) * (z ^ 3 * Gker 3 z)| ≤ 360 / z := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      calc (6 : ℝ) * |z ^ 3 * Gker 3 z| ≤ 6 * (60 / z) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 360 / z := by rw [mul_div_assoc']; norm_num
    calc |z ^ 1 * Gker 1 z + 7 * (z ^ 2 * Gker 2 z) + 6 * (z ^ 3 * Gker 3 z)
          + z ^ 4 * Gker 4 z|
        ≤ |z ^ 1 * Gker 1 z + 7 * (z ^ 2 * Gker 2 z) + 6 * (z ^ 3 * Gker 3 z)|
            + |z ^ 4 * Gker 4 z| := abs_add_le _ _
      _ ≤ (|z ^ 1 * Gker 1 z + 7 * (z ^ 2 * Gker 2 z)|
            + |(6 : ℝ) * (z ^ 3 * Gker 3 z)|) + |z ^ 4 * Gker 4 z| :=
            add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|z ^ 1 * Gker 1 z| + |(7 : ℝ) * (z ^ 2 * Gker 2 z)|)
            + |(6 : ℝ) * (z ^ 3 * Gker 3 z)|) + |z ^ 4 * Gker 4 z| :=
            add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ ((10 / z + 140 / z) + 360 / z) + 240 / z :=
            add_le_add (add_le_add (add_le_add h1 hB) hC) h4
      _ ≤ 1000 / z := by
          rw [show (10 : ℝ) / z + 140 / z + 360 / z + 240 / z = 750 / z by
            rw [← add_div, ← add_div, ← add_div]; norm_num]
          exact div_le_div_of_nonneg_right (by norm_num) hzpos.le

end Work.FTS.LocData
