import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs

/-!
# A support point witnesses `DLp 2 (nv e a b y) a b`

If `y` is a unit point at `2` at which `2 ^ (m + nv e a b y - 1) ∣ N(y)`
(`m = cubeLevel 2 e`, `N = critN a b`, `nv e a b y` the capped `2`-adic valuation of `N'(y)`),
then `y` itself is a double-critical witness at level `nv e a b y`:

* `2 ^ nv ∣ N(y)`, because `nv ≤ m + nv - 1` as soon as `m ≥ 1` (true for `e ≥ 13`), so that the
  given divisibility at level `m + nv - 1` implies the one at level `nv`;
* `2 ^ nv ∣ N'(y)`, because `nv = vcap 2 T (|N'(y)|)` and `2 ^ vcap 2 T |z|` always divides `z`
  (either `z = 0`, or `vcap` is a minimum with the exact valuation).

This is the "support ⟹ `DLp`" step for the `p = 2` counting lemma.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

open Polynomial

/-- `2 ^ vcap 2 K |z|` divides the integer `z`: either `z = 0` (and `2 ^ K ∣ 0`), or `vcap` is the
minimum of the exact valuation of `|z|` with `K`. -/
lemma two_pow_vcap_dvd (K : ℕ) (z : ℤ) : ((2 ^ vcap 2 K z.natAbs : ℕ) : ℤ) ∣ z := by
  by_cases hz : z = 0
  · rw [hz]; exact dvd_zero _
  · have hne : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
    rw [vcap, if_neg hne]
    have hdvd : 2 ^ min (padicValNat 2 z.natAbs) K ∣ z.natAbs :=
      dvd_trans (pow_dvd_pow 2 (min_le_left _ _)) pow_padicValNat_dvd
    exact dvd_trans (Nat.cast_dvd_cast hdvd) (Int.natAbs_dvd.mpr (dvd_refl z))

theorem dlp_of_supp {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 2 y a b)
    (hN : ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)) :
    DLp 2 (nv e a b y) a b := by
  -- `m = cubeLevel 2 e ≥ 1` for `e ≥ 13`, hence `nv ≤ m + nv - 1`.
  have hm : 1 ≤ cubeLevel 2 e := by
    simp only [cubeLevel]
    exact Nat.le_div_iff_mul_le (by norm_num : 0 < 3) |>.mpr (by omega)
  refine ⟨y, hy, ?_, ?_⟩
  · have hle : nv e a b y ≤ cubeLevel 2 e + nv e a b y - 1 := by omega
    exact dvd_trans (Nat.cast_dvd_cast (pow_dvd_pow 2 hle)) hN
  · exact two_pow_vcap_dvd (capLevel 2 e) ((critN a b).derivative.eval (y : ℤ))

end Work.LinnikBurgess.lfSmall
