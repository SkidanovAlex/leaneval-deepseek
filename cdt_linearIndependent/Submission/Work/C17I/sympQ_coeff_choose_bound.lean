import Mathlib
import Submission.Work.CPull.sympQ

/-!
# The coefficient bound `|[yⁿ] P_{n+j}| ≤ 2·C(n,j)`

`Work.CPull.sympQ m` is the symmetrised power `P_m(y) = x^m + φ(x)^m` written in the
symmetrisation coordinate `y = x²/(x-1)`; it satisfies `P_0 = 2`, `P_1 = y`,
`P_{m+2} = y·P_{m+1} − y·P_m`.

The main result of this file is the sharp-looking coefficient bound

`|[yⁿ] P_{n+j}| ≤ 2·C(n,j)`.

The proof works with the "Pascal weight"

`W m n := C(n, m-n)` for `n ≤ m` and `0` otherwise,

which is exactly the quantity we want (`W (n+j) n = C(n,j)`).  The coefficient sequence
`φ(m,n) = [yⁿ]P_m` obeys the recurrence `φ(m,n) = φ(m-1,n-1) − φ(m-2,n-1)` for `m ≥ 2`,
`n ≥ 1`, and the weight obeys Pascal's rule `W m n = W (m-1) (n-1) + W (m-2) (n-1)`;
a two-step induction on `m` (over all `n` simultaneously) then gives `|φ(m,n)| ≤ 2·W m n`.
-/

open scoped BigOperators

namespace Work.C17I

open PowerSeries

/-- The Pascal weight: `C(n, m-n)` when `n ≤ m`, and `0` otherwise. -/
noncomputable def W (m n : ℕ) : ℝ :=
  if n ≤ m then (Nat.choose n (m - n) : ℝ) else 0

lemma W_of_le {m n : ℕ} (h : n ≤ m) : W m n = (Nat.choose n (m - n) : ℝ) := if_pos h

lemma W_of_lt {m n : ℕ} (h : m < n) : W m n = 0 := if_neg (not_le.mpr h)

/-- Pascal's rule for the weight `W`. -/
lemma W_pascal (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    W m n = W (m - 1) (n - 1) + W (m - 2) (n - 1) := by
  by_cases hnm : n ≤ m
  · rw [W_of_le hnm, W_of_le (show n - 1 ≤ m - 1 by omega)]
    rcases Nat.eq_zero_or_pos (m - n) with hk | hk
    · have hA : (m - 1) - (n - 1) = 0 := by omega
      have hB : m - 2 < n - 1 := by omega
      rw [hA, W_of_lt hB, hk]
      simp
    · have hsub1 : (m - 1) - (n - 1) = m - n := by omega
      have hle2 : n - 1 ≤ m - 2 := by omega
      have hsub2 : (m - 2) - (n - 1) = m - n - 1 := by omega
      rw [hsub1, W_of_le hle2, hsub2]
      have hpas := Nat.choose_succ_succ' (n - 1) (m - n - 1)
      have h1 : n - 1 + 1 = n := by omega
      have h2 : m - n - 1 + 1 = m - n := by omega
      rw [h1, h2] at hpas
      rw [hpas]
      push_cast
      ring
  · have hmn : m < n := by omega
    rw [W_of_lt hmn, W_of_lt (show m - 1 < n - 1 by omega),
      W_of_lt (show m - 2 < n - 1 by omega)]
    ring

/-- Coefficient bound for all symmetrised powers, in the sharp weight `W`. -/
lemma coeff_bound_key : ∀ m n : ℕ,
    |((PowerSeries.coeff n (Work.CPull.sympQ m) : ℚ) : ℝ)| ≤ 2 * W m n := by
  intro m
  refine Nat.twoStepInduction (motive := fun m => ∀ n : ℕ,
    |((PowerSeries.coeff n (Work.CPull.sympQ m) : ℚ) : ℝ)| ≤ 2 * W m n) ?_ ?_ ?_ m
  · intro n
    have h2 : Work.CPull.sympQ 0 = PowerSeries.C (2 : ℚ) := by
      rw [show Work.CPull.sympQ 0 = (2 : PowerSeries ℚ) from rfl,
        PowerSeries.C_eq_algebraMap]
      exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm
    rw [h2, PowerSeries.coeff_C]
    rcases n with _ | n
    · simp [W]
    · rw [if_neg (by omega : ¬ ((n + 1) = 0))]
      have hW : W 0 (n + 1) = 0 := by
        rw [W_of_lt (by omega : 0 < n + 1)]
      rw [hW]
      simp
  · intro n
    rw [show Work.CPull.sympQ 1 = (X : PowerSeries ℚ) from rfl, PowerSeries.coeff_X]
    rcases n with _ | _ | n
    · simp [W]
    · simp [W]
    · rw [if_neg (by omega : ¬ ((n + 2) = 1))]
      have hW : W 1 (n + 2) = 0 := W_of_lt (by omega)
      rw [hW]
      simp
  · intro k ih1 ih2 n
    rcases n with _ | j
    · rw [show Work.CPull.sympQ (k + 2)
          = X * Work.CPull.sympQ (k + 1) - X * Work.CPull.sympQ k from rfl,
        map_sub (PowerSeries.coeff (R := ℚ) 0),
        PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul, sub_zero]
      have hW : W (k + 2) 0 = 0 := by
        rw [W_of_le (Nat.zero_le _)]
        simp
      rw [hW]
      simp
    · have hcoeff : PowerSeries.coeff (j + 1) (Work.CPull.sympQ (k + 2))
          = PowerSeries.coeff j (Work.CPull.sympQ (k + 1))
            - PowerSeries.coeff j (Work.CPull.sympQ k) := by
        rw [show Work.CPull.sympQ (k + 2)
              = X * Work.CPull.sympQ (k + 1) - X * Work.CPull.sympQ k from rfl,
            map_sub (PowerSeries.coeff (R := ℚ) (j + 1)),
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      rw [hcoeff]
      have hcast : (((PowerSeries.coeff j (Work.CPull.sympQ (k + 1))
            - PowerSeries.coeff j (Work.CPull.sympQ k) : ℚ) : ℝ))
          = ((PowerSeries.coeff j (Work.CPull.sympQ (k + 1)) : ℚ) : ℝ)
            - ((PowerSeries.coeff j (Work.CPull.sympQ k) : ℚ) : ℝ) := by
        push_cast; ring
      rw [hcast]
      calc |((PowerSeries.coeff j (Work.CPull.sympQ (k + 1)) : ℚ) : ℝ)
              - ((PowerSeries.coeff j (Work.CPull.sympQ k) : ℚ) : ℝ)|
          ≤ |((PowerSeries.coeff j (Work.CPull.sympQ (k + 1)) : ℚ) : ℝ)|
              + |((PowerSeries.coeff j (Work.CPull.sympQ k) : ℚ) : ℝ)| := abs_sub _ _
        _ ≤ 2 * W (k + 1) j + 2 * W k j := add_le_add (ih2 j) (ih1 j)
        _ = 2 * W (k + 2) (j + 1) := by
              have hp : W (k + 2) (j + 1) = W (k + 1) j + W k j := by
                have h := W_pascal (k + 2) (j + 1) (by omega) (by omega)
                simpa using h
              rw [hp]; ring

theorem sympQ_coeff_choose_bound (n j : ℕ) :
    |((((PowerSeries.coeff n (Work.CPull.sympQ (n + j)) : ℚ)) : ℝ))|
      ≤ 2 * (Nat.choose n j : ℝ) := by
  have h := coeff_bound_key (n + j) n
  have hW : W (n + j) n = (Nat.choose n j : ℝ) := by
    rw [W_of_le (Nat.le_add_right n j), Nat.add_sub_cancel_left]
  rw [hW] at h
  exact h

end Work.C17I
