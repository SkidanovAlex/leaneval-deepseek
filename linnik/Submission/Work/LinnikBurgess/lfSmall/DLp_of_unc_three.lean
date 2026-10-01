import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.DLp_of_unc

/-!
# The `p = 3` instance of "a support point with `nval y < T` witnesses `DLp`"

`Work.LinnikBurgess.DLp_of_unc` proves, for a prime `p ≥ 5` and `e ≥ 2`, that a support point `y`
of Lemma A whose capped Wronskian valuation `nval y` is below `T = capLevel p e` witnesses
`DLp p (nval y) a b`.

The argument it uses never touches the hypotheses `5 ≤ p` and `2 ≤ e`: it only needs

* `SuppTransfer p e a b`, which turns `b_y = min (nval y) T` into `b_y = nval y` when
  `nval y < T`, and gives `p^(m + b_y) ∣ N(y)` (with `m = cubeLevel p e`), hence `p^(nval y) ∣ N(y)`;
* `nval y < T` to force `N'(y) ≠ 0` and to identify `nval y` with the exact `p`-adic valuation
  `v_p(|N'(y)|)`, hence `p^(nval y) ∣ N'(y)`.

Since `T = capLevel 3 e ≤ e` and `3 ≠ 2`, the `p = 3` case needed by the small-prime counting
lemma is the same statement, so we record the general form here (valid for *every* `p`, with no
primality or size hypothesis) and specialise it to `p = 3`.
-/

open Polynomial

set_option linter.unusedVariables false

namespace Work.LinnikBurgess.lfSmall

open Work.LinnikBurgess

/-- The general "uncapped support point witnesses `DLp`" step, with no hypothesis on `p`.

If `y` is a support point, `SuppTransfer` holds, and `nval y < capLevel p e`, then `y` itself is a
double-critical witness at level `nval y`. -/
theorem DLp_of_unc_gen {p e : ℕ} (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : suppPred p e a b y) (hbt : SuppTransfer p e a b)
    (hlt : nval p e a b y < capLevel p e) :
    DLp p (nval p e a b y) a b := by
  obtain ⟨hbval, hNdvd⟩ := hbt y hy
  obtain ⟨hunit, _⟩ := hy
  -- `b_y = min (nval y) T = nval y` because `nval y < T`.
  have hbv : bval p e a b y = nval p e a b y := by
    rw [hbval, min_eq_left (le_of_lt hlt)]
  -- `p ^ (nval y) ∣ N(y)` from `p ^ (m + b_y) ∣ N(y)` and `nval y ≤ m + b_y`.
  have hN : ((p ^ nval p e a b y : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
    rw [hbv] at hNdvd
    exact dvd_trans
      (Nat.cast_dvd_cast (pow_dvd_pow p (Nat.le_add_left (nval p e a b y) (cubeLevel p e)))) hNdvd
  -- `nval y < T` forces `N'(y) ≠ 0`.
  have hN'ne : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
    intro h
    rw [nval, if_pos h] at hlt
    omega
  have hnval : nval p e a b y
      = padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs := by
    rw [nval, if_neg hN'ne]
  -- `p ^ (nval y) ∣ N'(y)`.
  have hN' : ((p ^ nval p e a b y : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
    have hk : (p ^ padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ)
        ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs := pow_padicValNat_dvd
    have hkz : ((p ^ padicValNat p ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ) : ℤ)
        ∣ (critN a b).derivative.eval (y : ℤ) :=
      dvd_trans (Nat.cast_dvd_cast hk) (Int.natAbs_dvd.mpr (dvd_refl _))
    rwa [hnval]
  exact ⟨y, hunit, hN, hN'⟩

/-- The `p = 3` case: a support point of the three-adic reduction with `nval y < capLevel 3 e`
witnesses `DLp 3 (nval y) a b`. -/
theorem DLp_of_unc_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : suppPred 3 e a b y) (hbt : SuppTransfer 3 e a b)
    (hlt : nval 3 e a b y < capLevel 3 e) :
    DLp 3 (nval 3 e a b y) a b :=
  DLp_of_unc_gen (p := 3) (e := e) a b hy hbt hlt

end Work.LinnikBurgess.lfSmall
