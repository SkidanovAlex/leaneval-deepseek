import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.critN_shifts
import Submission.Work.LinnikBurgess.critN_content_iff
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.defect1_mul_Uval
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq

/-!
# Vocabulary for the `p = 2` counting lemma (`lfSmall/counting_two`)

This module collects the notions used by the proof of

`Work.LinnikBurgess.lfSmall.counting_two`:
`gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b` for `e ≥ 13`.

The right–hand side of Lemma A₂ is the sum, over `y < 2^m` (`m = cubeLevel 2 e`) of the weight
`2 ^ (b_y / 2)` supported on the *unit* points `y` at which

* `2 ^ (m + b_y - 1) ∣ D₁(y)`  (i.e. `2 ^ (m + b_y - 1) ∣ N(y)`, `N = critN a b`, `D₁ = N/(f_a f_b)`),
* `b_y = vcap 2 (e - 2 m) (D₂(y))` (the *capped* `2`-adic valuation of the second defect).

The transfer lemmas of `two_transfer.lean` show that on the support one has

* `b_y = nv e a b y`  (`nv` below: the capped `2`-adic valuation of `N'(y)`),
* `2 ^ (m + b_y - 1) ∣ N(y)` as an integer divisibility,

so the support splits by the value `s = nv e a b y` into the `lvlSet2` (for `s < T`) and the
`capSet2` (for `s = T`), `T = capLevel 2 e`, and each of these witnesses `DLp 2 s a b`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

/-- `m = cubeLevel 2 e`: the level of the stationary-phase sum for `p = 2`. -/
noncomputable def mlvl (e : ℕ) : ℕ := cubeLevel 2 e

/-- `T = capLevel 2 e = e - 2 * m`: the cap level. -/
noncomputable def Tlvl (e : ℕ) : ℕ := capLevel 2 e

/-- `L = m + T - 1 = e - m - 1`: the level at which `N(y)` is required to vanish on the support. -/
noncomputable def Lvl (e : ℕ) : ℕ := cubeLevel 2 e + capLevel 2 e - 1

/-- The capped `2`-adic valuation of `N'(y)` (`N = critN a b`), with the convention that
`N'(y) = 0` gives the cap `T`; this is the level `b_y` of Lemma A₂ on the support. -/
noncomputable def nv (e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : ℕ :=
  vcap 2 (capLevel 2 e) ((critN a b).derivative.eval (y : ℤ)).natAbs

/-- The support of Lemma A₂, re-expressed through `critN`: unit points `y < 2^m` with
`2 ^ (m + nv - 1) ∣ N(y)`. -/
noncomputable def suppSet2 (e : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (Finset.range (2 ^ cubeLevel 2 e)).filter (fun y =>
    UnitAt 2 y a b ∧ ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ))

/-- The part of the support of level `s < T`: unit points `y < 2^m` with `2 ^ (m + s - 1) ∣ N(y)`
and `v₂(N'(y)) = s` exactly. -/
noncomputable def lvlSet2 (e s : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (Finset.range (2 ^ cubeLevel 2 e)).filter (fun y =>
    UnitAt 2 y a b ∧ ((2 ^ (cubeLevel 2 e + s - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)
      ∧ (critN a b).derivative.eval (y : ℤ) ≠ 0
      ∧ padicValNat 2 ((critN a b).derivative.eval (y : ℤ)).natAbs = s)

/-- The cap part of the support: unit points `y < 2^m` with `2 ^ L ∣ N(y)` and `2 ^ T ∣ N'(y)`. -/
noncomputable def capSet2 (e : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (Finset.range (2 ^ cubeLevel 2 e)).filter (fun y =>
    UnitAt 2 y a b ∧ ((2 ^ Lvl e : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)
      ∧ ((2 ^ capLevel 2 e : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ))

/-- The `2`-adic content of `critN a b`: the largest `J` with `2 ^ J` dividing every coefficient. -/
noncomputable def contentV2 (a b : Fin 3 → ℕ) : ℕ :=
  ((critN a b).coeff 0).natAbs.gcd (((critN a b).coeff 1).natAbs.gcd
    (((critN a b).coeff 2).natAbs.gcd (((critN a b).coeff 3).natAbs.gcd
      ((critN a b).coeff 4).natAbs))) |> fun g => padicValNat 2 g

/-- The indicator of a proposition as a real number (classical logic). -/
noncomputable def ind (P : Prop) : ℝ := if P then 1 else 0

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind; split <;> norm_num

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind; split <;> norm_num

theorem ind_eq_one_of (P : Prop) (h : P) : ind P = 1 := by simp [ind, h]

theorem ind_eq_zero_of (P : Prop) (h : ¬ P) : ind P = 0 := by simp [ind, h]

theorem mul_ind {x : ℝ} {P : Prop} (h : P) : x * ind P = x := by rw [ind_eq_one_of P h, mul_one]

end Work.LinnikBurgess.lfSmall
