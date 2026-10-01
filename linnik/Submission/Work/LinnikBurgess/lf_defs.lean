import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.critN_shifts

/-!
# Definitions and arithmetic for Theorem L (U7) of the Burgess route

`Work.LinnikBurgess.localFactor_bound_ge5` bounds the cubic character correlation at a prime
power `p^e` (`p ≥ 5`) by `p^{e/2} · localFactor p e a b`.  The proof goes through Lemma A
(`corr6_primePow_gaussTwo_le`), whose right-hand side `gaussTwoRHS p e (cubeLevel p e) a b` is a
sum over `y < p^m` (`m = ⌈e/3⌉`) of weights supported on the stationary points of the two-term
stationary phase.

This file collects the notions used by that reduction, together with the elementary arithmetic of
`m = cubeLevel p e` and `T = capLevel p e` used throughout:

* `Uval a b y = f_a(y) · f_b(y)` and `Wval a b y = f_a'(y) f_b(y) + f_a(y) f_b'(y)`, the value and
  derivative of the product of the two cubics at `y`;
* `bval p e a b y = min (v_p(D₂(y)), T)`, the capped valuation of the second defect of Lemma A;
* `suppPred`/`suppSet`: the support condition and support set of `gaussTwoRHS`;
* `nval p e a b y = v_p(N'(y))` for the Wronskian `N = critN a b`, with the convention `T + 1`
  when `N'(y) = 0`;
* `uncSet`/`capSet`/`lvlSet`: the splits of the support according to `nval`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-- `U(y) = f_a(y) · f_b(y) = ∏_l (y + a_l) · ∏_l (y + b_l)`, evaluated at `y`. -/
def Uval (y : ℕ) (a b : Fin 3 → ℕ) : ℕ := sh3 y a * sh3 y b

/-- `U'(y) = f_a'(y) f_b(y) + f_a(y) f_b'(y)`, evaluated at `y`. -/
def Wval (y : ℕ) (a b : Fin 3 → ℕ) : ℕ := sh2 y a * sh3 y b + sh3 y a * sh2 y b

/-- `b_y`: the capped valuation of the second defect appearing in Lemma A. -/
noncomputable def bval (p e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : ℕ :=
  vcap p (capLevel p e) (defect2 p e a b y).val

/-- The support predicate of the stationary-phase sum (`gaussTwoRHS`). -/
def suppPred (p e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : Prop :=
  UnitAt p y a b ∧ p ^ (cubeLevel p e + bval p e a b y) ∣ (defect1 p e a b y).val

/-- The support set: the `y < p^m` contributing to `gaussTwoRHS p e m a b`. -/
noncomputable def suppSet (p e : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (Finset.range (p ^ cubeLevel p e)).filter (fun y => suppPred p e a b y)

/-- `v_p(N'(y))` for the Wronskian `N = critN a b`, with the convention `T + 1` when `N'(y) = 0`
(so that `min nval T = T` in that case, matching the capped valuation `bval`). -/
noncomputable def nval (p e : ℕ) (a b : Fin 3 → ℕ) (y : ℕ) : ℕ :=
  if (critN a b).derivative.eval (y : ℤ) = 0 then capLevel p e + 1
  else padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs

/-- The part of the support with `v_p(N'(y)) < T`. -/
noncomputable def uncSet (p e : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (suppSet p e a b).filter (fun y => nval p e a b y < capLevel p e)

/-- The part of the support with `T ≤ v_p(N'(y))` (including `N'(y) = 0`). -/
noncomputable def capSet (p e : ℕ) (a b : Fin 3 → ℕ) : Finset ℕ :=
  (suppSet p e a b).filter (fun y => capLevel p e ≤ nval p e a b y)

/-- The level sets of `nval` inside the support. -/
noncomputable def lvlSet (p e : ℕ) (a b : Fin 3 → ℕ) (s : ℕ) : Finset ℕ :=
  (suppSet p e a b).filter (fun y => nval p e a b y = s)

/-- The transfer statement supplied by `bval_transfer`: for every point of the support of Lemma A,
the capped second-defect valuation is the capped `v_p(N'(y))` and `p^(m + b_y)` divides `N(y)`.
This is bundled as a `Prop` so that the counting lemmas can take it as a hypothesis and be proved in
parallel with the transfer itself. -/
def SuppTransfer (p e : ℕ) (a b : Fin 3 → ℕ) : Prop :=
  ∀ y : ℕ, suppPred p e a b y →
    bval p e a b y = min (nval p e a b y) (capLevel p e)
      ∧ ((p ^ (cubeLevel p e + bval p e a b y) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)

/-! ### Arithmetic of `cubeLevel` and `capLevel` -/

theorem cubeLevel_eq {p : ℕ} (hp : 5 ≤ p) (e : ℕ) : cubeLevel p e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by omega)]

theorem capLevel_eq {p : ℕ} (hp : 5 ≤ p) (e : ℕ) : capLevel p e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_eq hp]

theorem one_le_cubeLevel {p e : ℕ} (hp : 5 ≤ p) (he : 1 ≤ e) : 1 ≤ cubeLevel p e := by
  rw [cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem e_le_three_mul_cubeLevel {p e : ℕ} (hp : 5 ≤ p) : e ≤ 3 * cubeLevel p e := by
  rw [cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem two_mul_cubeLevel_le {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) :
    2 * cubeLevel p e ≤ e := by
  rw [cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem capLevel_le_cubeLevel {p e : ℕ} (hp : 5 ≤ p) :
    capLevel p e ≤ cubeLevel p e := by
  rw [capLevel_eq hp, cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem capLevel_le_self {p e : ℕ} (hp : 5 ≤ p) : capLevel p e ≤ e := by
  rw [capLevel_eq hp]
  omega

theorem cubeLevel_add_capLevel {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) :
    cubeLevel p e + capLevel p e = e - cubeLevel p e := by
  rw [capLevel_eq hp, cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  have h2 : 2 * ((e + 2) / 3) ≤ e := by omega
  omega

theorem cubeLevel_le_self {p e : ℕ} (hp : 5 ≤ p) (he : 1 ≤ e) : cubeLevel p e ≤ e := by
  rw [cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem cubeLevel_add_capLevel' {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) :
    cubeLevel p e + capLevel p e + cubeLevel p e = e := by
  rw [cubeLevel_add_capLevel hp he]
  exact Nat.sub_add_cancel (cubeLevel_le_self hp (by omega))

theorem capLevel_le_cubeLevel_div {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) :
    e - cubeLevel p e ≤ 2 * cubeLevel p e := by
  rw [cubeLevel_eq hp]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

end Work.LinnikBurgess
