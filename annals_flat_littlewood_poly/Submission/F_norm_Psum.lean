import Mathlib
import Submission.RSPsum_defs
import Submission.F_Psum_stable
import Submission.F_Psum_small
import Submission.F_Qsum_small
import Submission.F_Psum_large
import Submission.F_Qsum_large

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

/-! ## Auxiliary real bounds -/

/-- `(√2)^2 = 2`. -/
lemma fnp_sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 :=
  Real.sq_sqrt (x := 2) (by norm_num)

/-- `3√2 ≥ 4`. -/
lemma fnp_three_sqrt_two_ge_four : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
  have h1 : (4 : ℝ) ^ 2 ≤ (3 * Real.sqrt 2) ^ 2 := by
    calc
      (4 : ℝ) ^ 2 = 16 := by norm_num
      _ ≤ (3 * Real.sqrt 2) ^ 2 := by
        rw [mul_pow, fnp_sqrt_two_sq]
        norm_num
  have hle : |(4 : ℝ)| ≤ |3 * Real.sqrt 2| := (sq_le_sq.mp h1)
  have hnonneg : 0 ≤ 3 * Real.sqrt 2 := by positivity
  have h4nn : 0 ≤ (4 : ℝ) := by norm_num
  rw [← abs_of_nonneg h4nn, ← abs_of_nonneg hnonneg]
  exact hle

/-- `4√2 ≤ 6`. -/
lemma fnp_four_sqrt_two_le_six : 4 * Real.sqrt 2 ≤ 6 := by
  have h1 : (4 * Real.sqrt 2) ^ 2 ≤ 6 ^ 2 := by
    calc
      (4 * Real.sqrt 2) ^ 2 = 16 * (Real.sqrt 2) ^ 2 := by ring
      _ = 32 := by rw [fnp_sqrt_two_sq]; norm_num
      _ ≤ 6 ^ 2 := by norm_num
  have hle : |4 * Real.sqrt 2| ≤ |(6 : ℝ)| := (sq_le_sq.mp h1)
  have hnonneg : 0 ≤ 4 * Real.sqrt 2 := by positivity
  rw [← abs_of_nonneg hnonneg, ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  exact hle

/-- `√(2^(t+1)) = √(2^t) * √2`. -/
lemma fnp_sqrt_pow_succ (t : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (t + 1)) = Real.sqrt ((2 : ℝ) ^ t) * Real.sqrt 2 := by
  calc
    Real.sqrt ((2 : ℝ) ^ (t + 1)) = Real.sqrt (((2 : ℝ) ^ t) * 2) := by rw [pow_succ]
    _ = Real.sqrt ((2 : ℝ) ^ t) * Real.sqrt 2 := by
        exact Real.sqrt_mul (x := (2 : ℝ) ^ t) (by positivity : 0 ≤ (2 : ℝ) ^ t) (2 : ℝ)

/-- `√(2^t) ≤ √(2^(t+1))`. -/
lemma fnp_sqrt_pow_mono (t : ℕ) :
    Real.sqrt ((2 : ℝ) ^ t) ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  apply Real.sqrt_le_sqrt
  rw [pow_succ]
  exact le_mul_of_one_le_right (by positivity : 0 ≤ (2 : ℝ) ^ t) (by norm_num : (1 : ℝ) ≤ 2)

/-- The bound improvement at a level step: `√(2^(t+1)) + 4√(2^t) ≤ 4√(2^(t+1))`. -/
lemma fnp_level_sum_bound (t : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (t + 1)) + 4 * Real.sqrt ((2 : ℝ) ^ t) ≤
      4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  have hs : 0 ≤ Real.sqrt ((2 : ℝ) ^ t) := Real.sqrt_nonneg _
  have hspl := fnp_sqrt_pow_succ t
  have hstep : 4 * Real.sqrt ((2 : ℝ) ^ t) ≤
      3 * (Real.sqrt ((2 : ℝ) ^ t) * Real.sqrt 2) := by
    have hm := mul_le_mul_of_nonneg_left fnp_three_sqrt_two_ge_four hs
    nlinarith
  rw [hspl]
  nlinarith [hstep]

/-- `4√(2^t) ≤ 4√(2^(t+1))`. -/
lemma fnp_four_sqrt_pow_mono (t : ℕ) :
    4 * Real.sqrt ((2 : ℝ) ^ t) ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
  exact mul_le_mul_of_nonneg_left (fnp_sqrt_pow_mono t) (by norm_num : (0 : ℝ) ≤ 4)

/-- `4√(2m) ≤ 6√m`. -/
lemma fnp_four_sqrt_two_mul_le_six_sqrt (m : ℝ) :
    4 * Real.sqrt (2 * m) ≤ 6 * Real.sqrt m := by
  have hspl : Real.sqrt (2 * m) = Real.sqrt 2 * Real.sqrt m :=
    Real.sqrt_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2) m
  calc
    4 * Real.sqrt (2 * m) = 4 * (Real.sqrt 2 * Real.sqrt m) := by rw [hspl]
    _ = (4 * Real.sqrt 2) * Real.sqrt m := by ring
    _ ≤ 6 * Real.sqrt m := by
      exact mul_le_mul_of_nonneg_right fnp_four_sqrt_two_le_six (Real.sqrt_nonneg m)

/-- If `2^t ≤ 2m` then `4√(2^t) ≤ 6√m`. -/
lemma fnp_four_sqrt_pow_le_six_sqrt (m t : ℕ) (hpow : 2 ^ t ≤ 2 * m) :
    4 * Real.sqrt ((2 : ℝ) ^ t) ≤ 6 * Real.sqrt (m : ℝ) := by
  have hcast : ((2 ^ t : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hpow
  have hpowle : (2 : ℝ) ^ t ≤ 2 * (m : ℝ) := by
    simpa [Nat.cast_pow, Nat.cast_mul] using hcast
  have hs := Real.sqrt_le_sqrt hpowle
  calc
    4 * Real.sqrt ((2 : ℝ) ^ t) ≤ 4 * Real.sqrt (2 * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ 6 * Real.sqrt (m : ℝ) := fnp_four_sqrt_two_mul_le_six_sqrt (m : ℝ)

/-! ## Level bound for prefixes of `P` and `Q` -/

/-- For `m ≤ 2^t`, prefixes of `P t` and `Q t` of length `m` have sup-norm on the
unit circle bounded by `4√(2^t)`.  This is proved by induction on `t`, using the
Rudin-Shapiro decomposition (`Psum_small`, `Qsum_small`, `Psum_large`, `Qsum_large`). -/
lemma fnp_level_bound (t m : ℕ) (hm : m ≤ 2 ^ t) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(Psum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) ∧
    ‖(Qsum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) := by
  revert m
  induction t with
  | zero =>
      intro m hm
      have hml1 : m ≤ 1 := by simpa using hm
      have hm01 : m = 0 ∨ m = 1 := by omega
      constructor
      · rcases hm01 with rfl | rfl
        · simp [Psum_zero]
        · have hval : (Psum 0 1).eval z = 1 := by rw [Psum]; simp [P_zero]
          rw [hval]
          simp
      · rcases hm01 with rfl | rfl
        · simp [Qsum_zero]
        · have hval : (Qsum 0 1).eval z = 1 := by rw [Qsum]; simp [Q_zero]
          rw [hval]
          simp
  | succ t ih =>
      intro m hm
      by_cases hsmall : m ≤ 2 ^ t
      · have hP : ‖(Psum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) := (ih m hsmall).1
        constructor
        · rw [Psum_small t m hsmall]
          exact le_trans hP (fnp_four_sqrt_pow_mono t)
        · rw [Qsum_small t m hsmall]
          exact le_trans hP (fnp_four_sqrt_pow_mono t)
      · have hbig : 2 ^ t < m := Nat.lt_of_not_ge hsmall
        let m' := m - 2 ^ t
        have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by
          rw [pow_succ]
          rw [mul_comm]
        have hm'le : m' ≤ 2 ^ t := by
          dsimp [m']
          rw [hpow] at hm
          omega
        have hle2t : 2 ^ t ≤ m := le_of_lt hbig
        have hm_eq : m = 2 ^ t + m' := by
          dsimp [m']
          omega
        have hQ' : ‖(Qsum t m').eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) := (ih m' hm'le).2
        have hPeval : ‖(P t).eval z‖ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) := norm_P_eval_le t z hz
        have hXterm : ‖(X ^ 2 ^ t * Qsum t m').eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) := by
          have hev : (X ^ 2 ^ t * Qsum t m').eval z = z ^ 2 ^ t * (Qsum t m').eval z := by simp
          rw [hev]
          calc
            ‖z ^ 2 ^ t * (Qsum t m').eval z‖ = ‖z ^ 2 ^ t‖ * ‖(Qsum t m').eval z‖ := norm_mul _ _
            _ = ‖(Qsum t m').eval z‖ := by
              have hzpow : ‖z ^ 2 ^ t‖ = 1 := by
                rw [norm_pow, hz]
                simp
              rw [hzpow]
              simp
            _ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) := hQ'
        have hPsumL : Psum (t + 1) m = P t + X ^ 2 ^ t * Qsum t m' := by
          rw [hm_eq]
          exact Psum_large t m'
        have heval : (Psum (t + 1) m).eval z = (P t).eval z + (X ^ 2 ^ t * Qsum t m').eval z := by
          rw [hPsumL]
          simp
        have hPbound : ‖(Psum (t + 1) m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
          rw [heval]
          calc
            ‖(P t).eval z + (X ^ 2 ^ t * Qsum t m').eval z‖
                ≤ ‖(P t).eval z‖ + ‖(X ^ 2 ^ t * Qsum t m').eval z‖ := norm_add_le _ _
            _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) + 4 * Real.sqrt ((2 : ℝ) ^ t) :=
                add_le_add hPeval hXterm
            _ ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := fnp_level_sum_bound t
        have hQsumL : Qsum (t + 1) m = P t - X ^ 2 ^ t * Qsum t m' := by
          rw [hm_eq]
          exact Qsum_large t m'
        have hevalQ : (Qsum (t + 1) m).eval z = (P t).eval z - (X ^ 2 ^ t * Qsum t m').eval z := by
          rw [hQsumL]
          simp
        have hQbound : ‖(Qsum (t + 1) m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := by
          rw [hevalQ]
          calc
            ‖(P t).eval z - (X ^ 2 ^ t * Qsum t m').eval z‖
                ≤ ‖(P t).eval z‖ + ‖(X ^ 2 ^ t * Qsum t m').eval z‖ := norm_sub_le _ _
            _ ≤ Real.sqrt ((2 : ℝ) ^ (t + 1)) + 4 * Real.sqrt ((2 : ℝ) ^ t) :=
                add_le_add hPeval hXterm
            _ ≤ 4 * Real.sqrt ((2 : ℝ) ^ (t + 1)) := fnp_level_sum_bound t
        exact ⟨hPbound, hQbound⟩

/-! ## Prefix stability of `Q` -/

/-- For `t0 + 1 ≤ t`, coefficients of `Q t` below `2^t0` coincide with those of `P t0`. -/
lemma fnp_coeff_Q_eq_coeff_P_of_succ_le {t0 t i : ℕ} (ht : t0 + 1 ≤ t) (hi : i < 2 ^ t0) :
    (Q t).coeff i = (P t0).coeff i := by
  refine Nat.le_induction (m := t0 + 1) (P := fun n _ => (Q n).coeff i = (P t0).coeff i)
    ?base ?succ t ht
  · exact coeff_Q_extend t0 i hi
  · intro n htn ih
    calc
      (Q (n + 1)).coeff i = (P n).coeff i := coeff_Q_extend n i (by
        exact lt_of_lt_of_le hi (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega : t0 ≤ n)))
      _ = (P t0).coeff i := coeff_P_stable (by omega : t0 ≤ n) hi

/-- For `m ≤ 2^t0` and `t0 + 1 ≤ t`, the `Q`-prefix at level `t` equals the `P`-prefix
at level `t0`. -/
lemma fnp_Qsum_eq_Psum_of_succ_le {t0 t m : ℕ} (hm : m ≤ 2 ^ t0) (ht : t0 + 1 ≤ t) :
    Qsum t m = Psum t0 m := by
  rw [Qsum, Psum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < m := Finset.mem_range.mp hk
  have hk2 : k < 2 ^ t0 := lt_of_lt_of_le hklt hm
  congr 1
  rw [fnp_coeff_Q_eq_coeff_P_of_succ_le ht hk2]

/-! ## The level `log₂ m + 1` and final `6√m` bounds -/

/-- Shapiro's bound: for any `t` with `m ≤ 2^t`, the first `m` Rudin-Shapiro coefficients
form a prefix with sup-norm on the circle bounded by `6 * sqrt m`.

Proof sketch.  For `m = 0` it is trivial.  For `m ≥ 1` let `t0 := Nat.log2 m + 1`.
One has `2 ^ (t0 - 1) ≤ m` (this is `2 ^ (Nat.log2 m) ≤ m`) and `m ≤ 2 ^ t0`
(because `m < 2 ^ (Nat.log2 m + 1)`; relevant names: `Nat.pow_log2_le_self`,
`Nat.lt_pow_succ_log2_self` or similar).
By `Psum_stable` (both directions, since `t` and `t0` are comparable and `m` fits in both
levels) the prefix `Psum t m` equals `Psum t0 m`.  Apply `Psum_bound_level` at level `t0`
to get `‖(Psum t m).eval z‖ ≤ 4 * sqrt (2 ^ t0)`.  Finally
`2 ^ t0 = 2 * 2 ^ (Nat.log2 m) ≤ 2 * m`, hence `4 * sqrt (2 ^ t0) ≤ 4 * sqrt (2 * m)
= 4 * sqrt 2 * sqrt m ≤ 6 * sqrt m` (as `4 * sqrt 2 ≤ 6`). -/
lemma norm_Psum_eval_le (t m : ℕ) (hm : m ≤ 2 ^ t) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(Psum t m).eval z‖ ≤ 6 * Real.sqrt m := by
  by_cases hm0 : m = 0
  · subst m
    simp [Psum_zero]
  · let t0 := m.log2 + 1
    have ht0pow : m ≤ 2 ^ t0 := by
      dsimp [t0]
      have hlt : m < 2 ^ (m.log2 + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) m
        simpa [Nat.log2_eq_log_two] using h
      exact le_of_lt hlt
    have ht0mul : 2 ^ t0 ≤ 2 * m := by
      dsimp [t0]
      have hlow : 2 ^ m.log2 ≤ m := by
        have h := Nat.pow_log_le_self (b := 2) (x := m) hm0
        simpa [Nat.log2_eq_log_two] using h
      calc
        2 ^ (m.log2 + 1) = 2 * 2 ^ m.log2 := by rw [pow_succ]; rw [mul_comm]
        _ ≤ 2 * m := Nat.mul_le_mul_left 2 hlow
    have hPstab : Psum t m = Psum t0 m := by
      by_cases h : t0 ≤ t
      · exact Psum_stable ht0pow h
      · have htle : t ≤ t0 := le_of_not_ge h
        exact (Psum_stable hm htle).symm
    have heval : (Psum t m).eval z = (Psum t0 m).eval z := by rw [hPstab]
    have hbnd : ‖(Psum t0 m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t0) :=
      (fnp_level_bound t0 m ht0pow z hz).1
    have hbnd' : ‖(Psum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t0) := by
      rw [heval]
      exact hbnd
    exact le_trans hbnd' (fnp_four_sqrt_pow_le_six_sqrt m t0 ht0mul)

/-- Same bound for the `Q`-prefix. -/
lemma norm_Qsum_eval_le (t m : ℕ) (hm : m ≤ 2 ^ t) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(Qsum t m).eval z‖ ≤ 6 * Real.sqrt m := by
  by_cases hm0 : m = 0
  · subst m
    simp [Qsum_zero]
  · let t0 := m.log2 + 1
    have ht0pow : m ≤ 2 ^ t0 := by
      dsimp [t0]
      have hlt : m < 2 ^ (m.log2 + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) m
        simpa [Nat.log2_eq_log_two] using h
      exact le_of_lt hlt
    have ht0mul : 2 ^ t0 ≤ 2 * m := by
      dsimp [t0]
      have hlow : 2 ^ m.log2 ≤ m := by
        have h := Nat.pow_log_le_self (b := 2) (x := m) hm0
        simpa [Nat.log2_eq_log_two] using h
      calc
        2 ^ (m.log2 + 1) = 2 * 2 ^ m.log2 := by rw [pow_succ]; rw [mul_comm]
        _ ≤ 2 * m := Nat.mul_le_mul_left 2 hlow
    by_cases h : t0 + 1 ≤ t
    · have hQs : Qsum t m = Psum t0 m := fnp_Qsum_eq_Psum_of_succ_le ht0pow h
      have heval : (Qsum t m).eval z = (Psum t0 m).eval z := by rw [hQs]
      have hbnd0 : ‖(Psum t0 m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t0) :=
        (fnp_level_bound t0 m ht0pow z hz).1
      have hbnd : ‖(Qsum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t0) := by
        rw [heval]
        exact hbnd0
      exact le_trans hbnd (fnp_four_sqrt_pow_le_six_sqrt m t0 ht0mul)
    · have htle : t ≤ t0 := by omega
      have hbnd0 : ‖(Qsum t m).eval z‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ t) :=
        (fnp_level_bound t m hm z hz).2
      have hpow_le : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ t0 :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) htle
      have hsqrt_le : Real.sqrt ((2 : ℝ) ^ t) ≤ Real.sqrt ((2 : ℝ) ^ t0) :=
        Real.sqrt_le_sqrt hpow_le
      have hfour : 4 * Real.sqrt ((2 : ℝ) ^ t) ≤ 4 * Real.sqrt ((2 : ℝ) ^ t0) :=
        mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
      exact le_trans (le_trans hbnd0 hfour) (fnp_four_sqrt_pow_le_six_sqrt m t0 ht0mul)

end RudinShapiro
end Submission
