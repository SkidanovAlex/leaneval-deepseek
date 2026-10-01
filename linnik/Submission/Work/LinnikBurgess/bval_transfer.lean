import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.defect1_mul_Uval
import Submission.Work.LinnikBurgess.defect2_mul_Uval_sq
import Submission.Work.LinnikBurgess.val_dvd_iff_castHom_eq_zero
import Submission.Work.LinnikBurgess.dvd_defect1_congr
import Submission.Work.LinnikBurgess.dvd_defect2_congr
import Submission.Work.LinnikBurgess.cubeLevel_add_bval_le

/-!
# The support transfer for Lemma A (`bval_transfer`)

Lemma A of the Burgess route sums over the points `y < p^m` (`m = cubeLevel p e`) which are units
at `p` and satisfy `p^(m + b_y) ∣ D₁(y)` where `b_y = vcap p T (D₂(y)).val`, `T = capLevel p e`.

This file shows that on this support the capped second-defect valuation is the capped valuation of
`N'(y)` (`N = critN a b` the Wronskian), `b_y = min (nval y) T`, and that `p^(m+b_y) ∣ N(y)`.

The two inputs are the exact identities in `ZMod (p^e)`
`D₁(y)·U(y) = N(y)` and `D₂(y)·U(y)² = −N'(y)·U(y) + N(y)·W(y)` (`U = Uval`, `W = Wval`), with `U`
a unit modulo `p^e`; read as integral congruences they determine all the `p`-adic valuations.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-! ### Temporary statements of the delegated lemmas

The three component lemmas `dvd_defect1_congr`, `dvd_defect2_congr` (the two defect identities read
as integral congruences) and `cubeLevel_add_bval_le` (arithmetic of the levels) are proved in
separate modules and imported at the top. -/

/-! ### Elementary lemmas -/

/-- `m + T ≤ e` for `m = cubeLevel p e`, `T = capLevel p e`, `p ≥ 5`, `e ≥ 2`. -/
lemma cubeLevel_add_capLevel_le {p e : ℕ} (hp5 : 5 ≤ p) (he : 2 ≤ e) :
    cubeLevel p e + capLevel p e ≤ e := by
  rw [cubeLevel_add_capLevel hp5 he]
  exact Nat.sub_le _ _

/-- If `y` is a unit at `p` then `U(y) = f_a(y) f_b(y)` is coprime to `p`. -/
lemma not_dvd_Uval {p : ℕ} (hp : p.Prime) {y : ℕ} {a b : Fin 3 → ℕ} (hy : UnitAt p y a b) :
    ¬ p ∣ Uval y a b := by
  unfold Uval sh3
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact (hy 0).1 h
      · exact (hy 1).1 h
    · exact (hy 2).1 h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact (hy 0).2 h
      · exact (hy 1).2 h
    · exact (hy 2).2 h

/-! ### A small `p`-adic kit for `ℤ` -/

lemma isCoprime_pow_of_not_dvd {p : ℕ} [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (j : ℕ) :
    IsCoprime ((p : ℤ) ^ j) u := by
  have hnat : ¬ p ∣ u.natAbs := fun h =>
    hu (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.Coprime.pow_left j ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hnat)

/-- Cancelling a factor coprime to `p` from a `p`-power divisibility. -/
lemma dvd_of_dvd_mul_of_not_dvd {p : ℕ} [Fact p.Prime] {j : ℕ} {A u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ j ∣ A * u) : (p : ℤ) ^ j ∣ A :=
  (isCoprime_pow_of_not_dvd hu j).dvd_of_dvd_mul_right h

/-- The same, with the coprime factor squared. -/
lemma dvd_of_dvd_mul_sq_of_not_dvd {p : ℕ} [Fact p.Prime] {j : ℕ} {A u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ j ∣ A * u ^ 2) : (p : ℤ) ^ j ∣ A := by
  have hcop : IsCoprime ((p : ℤ) ^ j) (u ^ 2) := (isCoprime_pow_of_not_dvd hu j).pow_right
  exact hcop.dvd_of_dvd_mul_right h

/-- The `p`-power divisibility criterion for the `p`-adic valuation of an integer. -/
lemma padicValInt_dvd_iff_le {p : ℕ} [Fact p.Prime] {z : ℤ} (hz : z ≠ 0) (j : ℕ) :
    (p : ℤ) ^ j ∣ z ↔ j ≤ padicValInt p z := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast]
  exact padicValNat_dvd_iff_le (by rwa [Int.natAbs_ne_zero])

/-! ### The two valuations on the support, in `ℤ` form -/

/-- `bval` in the shape used by the transfer: `if D₂(y).val = 0` it is the cap, else the capped
valuation of `D₂(y).val`, now read as an integer. -/
lemma bval_eq {p e : ℕ} (a b : Fin 3 → ℕ) (y : ℕ) :
    bval p e a b y
      = if (((defect2 p e a b y).val : ℕ) : ℤ) = 0 then capLevel p e
        else min (padicValInt p (((defect2 p e a b y).val : ℕ) : ℤ)) (capLevel p e) := by
  rw [bval, vcap]
  by_cases h : (defect2 p e a b y).val = 0
  · have h' : (((defect2 p e a b y).val : ℕ) : ℤ) = 0 := by exact_mod_cast h
    rw [if_pos h', if_pos h]
  · have h' : ¬ ((((defect2 p e a b y).val : ℕ) : ℤ) = 0) := by
      rw [Int.natCast_eq_zero]; exact h
    rw [if_neg h', if_neg h, padicValInt.of_nat]

/-- `nval` in `ℤ` form: the capped valuation of `N'(y)` with the convention `T + 1` for `N'(y) = 0`. -/
lemma nval_eq {p e : ℕ} (a b : Fin 3 → ℕ) (y : ℕ) :
    nval p e a b y
      = if (critN a b).derivative.eval (y : ℤ) = 0 then capLevel p e + 1
        else padicValInt p ((critN a b).derivative.eval (y : ℤ)) := rfl

/-- A `T`-th power of `p` dividing `N'(y)` forces `T ≤ nval y`. -/
lemma le_nval_of_dvd {p T : ℕ} [Fact p.Prime] {nn' : ℤ} (h : ((p : ℤ) ^ T) ∣ nn') :
    T ≤ (if nn' = 0 then T + 1 else padicValInt p nn') := by
  by_cases hn : nn' = 0
  · rw [if_pos hn]; omega
  · rw [if_neg hn]; exact (padicValInt_dvd_iff_le hn T).mp h

/-! ### The valuation comparison

Abstract form: given the integral congruence
`p^e ∣ d₂ u² + n' u − n w`, a unit coefficient `u` and `p^(m+b_y) ∣ n`, the two defining shapes of
`b_y` and of `nval` agree. -/

lemma transfer_core {p : ℕ} [Fact p.Prime] {e m T b : ℕ} {d2 u w nn nn' : ℤ}
    (hm : 1 ≤ m) (hmT : m + T ≤ e)
    (hb : b = if d2 = 0 then T else min (padicValInt p d2) T)
    (hcong : ((p : ℤ) ^ e) ∣ d2 * u ^ 2 + nn' * u - nn * w)
    (hu : ¬ (p : ℤ) ∣ u)
    (hnn : ((p : ℤ) ^ (m + b)) ∣ nn) :
    b = min (if nn' = 0 then T + 1 else padicValInt p nn') T := by
  have hTe : T ≤ e := le_trans (Nat.le_add_left T m) hmT
  have hTm : T ≤ m + T := Nat.le_add_left T m
  rw [hb] at hnn ⊢
  rcases eq_or_ne d2 0 with hd2 | hd2
  · -- `D₂(y).val = 0`: then `b = T` and `p^T ∣ N'(y)`
    rw [if_pos hd2] at hnn ⊢
    have hPT : ((p : ℤ) ^ T) ∣ nn' := by
      have h1 : ((p : ℤ) ^ T) ∣ nn * w :=
        dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hTm) hnn) w
      have h2 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 := by
        rw [hd2, zero_mul]
        exact dvd_zero ((p : ℤ) ^ T)
      have h3 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
        dvd_trans (pow_dvd_pow _ hTe) hcong
      have h4 : ((p : ℤ) ^ T) ∣ nn' * u - (nn * w - d2 * u ^ 2) := by
        have hkey : nn' * u - (nn * w - d2 * u ^ 2) = d2 * u ^ 2 + nn' * u - nn * w := by ring
        rw [hkey]; exact h3
      have h5 : ((p : ℤ) ^ T) ∣ nn' * u := by
        have hkey : nn' * u
            = (nn' * u - (nn * w - d2 * u ^ 2)) + (nn * w - d2 * u ^ 2) := by ring
        rw [hkey]
        exact dvd_add h4 (dvd_sub h1 h2)
      exact dvd_of_dvd_mul_of_not_dvd hu h5
    rw [min_eq_right (le_nval_of_dvd hPT)]
  · rw [if_neg hd2] at hnn ⊢
    rcases lt_or_ge (padicValInt p d2) T with hk | hk
    · -- `v_p(D₂(y).val) = k < T`: then `b = k` and `v_p(N'(y)) = k` with `N'(y) ≠ 0`
      have hke : padicValInt p d2 + 1 ≤ e := by omega
      have hke' : padicValInt p d2 ≤ e := by omega
      rw [min_eq_left (le_of_lt hk)] at hnn
      have hPd : ((p : ℤ) ^ padicValInt p d2) ∣ d2 :=
        (padicValInt_dvd_iff_le hd2 _).mpr le_rfl
      have hPnn : ((p : ℤ) ^ padicValInt p d2) ∣ nn :=
        dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ m)) hnn
      have hPdU : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 := dvd_mul_of_dvd_left hPd _
      have hB : ((p : ℤ) ^ padicValInt p d2) ∣ nn * w - d2 * u ^ 2 :=
        dvd_sub (dvd_mul_of_dvd_left hPnn w) hPdU
      have hcong' : ((p : ℤ) ^ padicValInt p d2) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
        dvd_trans (pow_dvd_pow _ hke') hcong
      have h4 : ((p : ℤ) ^ padicValInt p d2) ∣ nn' * u - (nn * w - d2 * u ^ 2) := by
        have hkey : nn' * u - (nn * w - d2 * u ^ 2) = d2 * u ^ 2 + nn' * u - nn * w := by ring
        rw [hkey]; exact hcong'
      have h5 : ((p : ℤ) ^ padicValInt p d2) ∣ nn' * u := by
        have hkey : nn' * u
            = (nn' * u - (nn * w - d2 * u ^ 2)) + (nn * w - d2 * u ^ 2) := by ring
        rw [hkey]
        exact dvd_add h4 hB
      have hPnn' : ((p : ℤ) ^ padicValInt p d2) ∣ nn' := dvd_of_dvd_mul_of_not_dvd hu h5
      have hnot : ¬ ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' := by
        intro hbad
        have h1 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' * u := dvd_mul_of_dvd_left hbad u
        have h2 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn * w :=
          dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ (by omega)) hnn) w
        have h3 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
          dvd_trans (pow_dvd_pow _ hke) hcong
        have h4' : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn' * u - (nn * w - d2 * u ^ 2) := by
          have hkey : nn' * u - (nn * w - d2 * u ^ 2) = d2 * u ^ 2 + nn' * u - nn * w := by ring
          rw [hkey]; exact h3
        have h6 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ nn * w - d2 * u ^ 2 := by
          have hkey : nn * w - d2 * u ^ 2
              = nn' * u - (nn' * u - (nn * w - d2 * u ^ 2)) := by ring
          rw [hkey]
          exact dvd_sub h1 h4'
        have h7 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 * u ^ 2 := by
          have hkey : d2 * u ^ 2 = nn * w - (nn * w - d2 * u ^ 2) := by ring
          rw [hkey]
          exact dvd_sub h2 h6
        have h8 : ((p : ℤ) ^ (padicValInt p d2 + 1)) ∣ d2 :=
          dvd_of_dvd_mul_sq_of_not_dvd hu h7
        have h9 := (padicValInt_dvd_iff_le hd2 (padicValInt p d2 + 1)).mp h8
        omega
      have hnz : nn' ≠ 0 := by
        intro hz
        exact hnot (by rw [hz]; exact dvd_zero _)
      have hval : padicValInt p nn' = padicValInt p d2 := by
        refine le_antisymm ?_ ?_
        · by_contra hlt
          exact hnot ((padicValInt_dvd_iff_le hnz _).mpr (not_le.mp hlt))
        · exact (padicValInt_dvd_iff_le hnz _).mp hPnn'
      rw [if_neg hnz, hval, min_eq_left (le_of_lt hk)]
    · -- `T ≤ v_p(D₂(y).val)`: then `b = T` and `p^T ∣ N'(y)`
      rw [min_eq_right hk] at hnn ⊢
      have hPT : ((p : ℤ) ^ T) ∣ nn' := by
        have h1 : ((p : ℤ) ^ T) ∣ nn * w :=
          dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hTm) hnn) w
        have h2 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 :=
          dvd_mul_of_dvd_left ((padicValInt_dvd_iff_le hd2 T).mpr hk) _
        have h3 : ((p : ℤ) ^ T) ∣ d2 * u ^ 2 + nn' * u - nn * w :=
          dvd_trans (pow_dvd_pow _ hTe) hcong
        have h4 : ((p : ℤ) ^ T) ∣ nn' * u - (nn * w - d2 * u ^ 2) := by
          have hkey : nn' * u - (nn * w - d2 * u ^ 2) = d2 * u ^ 2 + nn' * u - nn * w := by ring
          rw [hkey]; exact h3
        have h5 : ((p : ℤ) ^ T) ∣ nn' * u := by
          have hkey : nn' * u
              = (nn' * u - (nn * w - d2 * u ^ 2)) + (nn * w - d2 * u ^ 2) := by ring
          rw [hkey]
          exact dvd_add h4 (dvd_sub h1 h2)
        exact dvd_of_dvd_mul_of_not_dvd hu h5
      rw [min_eq_right (le_nval_of_dvd hPT)]

/-! ### The transfer on the support -/

/-- **The support condition in terms of the Wronskian** (`SuppTransfer p e a b`).  If `y` is in the
support of Lemma A's stationary-phase sum (`suppPred`, i.e. `y` is a unit at `p` and
`p^(m + b_y) ∣ defect1.val` with `m = cubeLevel p e`, `T = capLevel p e`,
`b_y = vcap p T (defect2 y).val`), then

* the capped second-defect valuation is the capped `v_p(N'(y))`: `b_y = min (nval y) T`, where
  `nval y = v_p(N'(y))` with the convention `T + 1` when `N'(y) = 0`;
* `p ^ (m + b_y) ∣ N(y)`.

Here `N = critN a b` is the Wronskian. -/
theorem bval_transfer {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) : SuppTransfer p e a b := by
  intro y hy
  obtain ⟨hunit, hsupp⟩ := hy
  have hp : p.Prime := Fact.out
  have hm : 1 ≤ cubeLevel p e := one_le_cubeLevel hp5 (by omega)
  have hmT : cubeLevel p e + capLevel p e ≤ e := cubeLevel_add_capLevel_le hp5 he
  have hmb : cubeLevel p e + bval p e a b y ≤ e := cubeLevel_add_bval_le hp5 he a b y
  have hc1 := dvd_defect1_congr (p := p) (e := e) a b hunit
  have hc2 := dvd_defect2_congr (p := p) (e := e) a b hunit
  -- `U(y)` is coprime to `p`
  have hu : ¬ (p : ℤ) ∣ (Uval y a b : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact not_dvd_Uval hp hunit
  -- `p^(m+b_y) ∣ N(y)`
  have hN : ((p : ℤ) ^ (cubeLevel p e + bval p e a b y)) ∣ (critN a b).eval (y : ℤ) := by
    have h1 : ((p : ℤ) ^ (cubeLevel p e + bval p e a b y))
        ∣ (defect1 p e a b y).val * (Uval y a b : ℤ) := by
      have h2 : ((p : ℤ) ^ (cubeLevel p e + bval p e a b y))
          ∣ (((defect1 p e a b y).val : ℕ) : ℤ) := by
        rw [← Nat.cast_pow]
        exact Int.natCast_dvd_natCast.mpr hsupp
      exact dvd_mul_of_dvd_left h2 _
    have h3 : ((p : ℤ) ^ (cubeLevel p e + bval p e a b y)) ∣ ((p : ℤ) ^ e) :=
      pow_dvd_pow _ hmb
    have h4 := dvd_trans h3 hc1
    have h5 := dvd_sub h1 h4
    have hkey : (critN a b).eval (y : ℤ)
        = (defect1 p e a b y).val * (Uval y a b : ℤ)
          - ((defect1 p e a b y).val * (Uval y a b : ℤ) - (critN a b).eval (y : ℤ)) := by ring
    rw [hkey]
    exact h5
  refine ⟨?_, ?_⟩
  · have hcore := transfer_core (p := p) (e := e) (m := cubeLevel p e) (T := capLevel p e)
      (b := bval p e a b y) (d2 := (((defect2 p e a b y).val : ℕ) : ℤ))
      (u := (Uval y a b : ℤ)) (w := (Wval y a b : ℤ))
      (nn := (critN a b).eval (y : ℤ)) (nn' := (critN a b).derivative.eval (y : ℤ))
      hm hmT (bval_eq a b y) hc2 hu hN
    rw [hcore, nval_eq]
  · rw [Nat.cast_pow]
    exact hN

end Work.LinnikBurgess
