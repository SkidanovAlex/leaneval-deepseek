import Mathlib
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log
import Submission.Vdw.SquarefullSum

open scoped BigOperators

set_option autoImplicit false

/-!
# Case-I tail sums over squarefull discriminants (CI-4, analytic layer)

The discrete layer (`SquarefullSum.lean`) bounds the squarefull sum by the
`(a,b)`-parametrized double sum with separated weights.  This module provides
the analytic inequalities that turn that double sum into a decaying tail:

* `nat_rpow_neg_le_one_div` / `sum_nat_rpow_neg_le_log`: for `s ≥ 1` and
  naturals, `Σ_{k ≤ A} k^(-s) ≤ 1 + log A` (the polylog growth is absorbed at
  the end by the positive exponent margin of Case I);
* `prod_gt_Y_rpow`: if `Y < m` (naturals, `1 ≤ Y`) and `t > 0`, then
  `1 ≤ m^t / Y^t`;
* **`pairWeight_tail_le`**: the constrained pair double sum
  `Σ_{a,b ≤ Z} [Y < a²b³] u(a)v(b)` is at most
  `(Σ_a u(a)·(a²)^t)(Σ_b v(b)·(b³)^t) / Y^t` for nonnegative `u,v` — the
  indicator-decay step of CI-4.

The full Case-I tail bound (combining this with the `ω`-color power-weight
lemma of the commons and the discrete transfer of `SquarefullSum`) will be
assembled on top of this module once the power-weighted ω lemma lands.
-/

namespace Submission.Vdw

/-- For naturals `1 ≤ k`, the power `k^(-s)` (real) with `s ≥ 1` is at most
`1/k`. -/
lemma nat_rpow_neg_le_one_div (k : ℕ) (hk : 1 ≤ k) {s : ℝ} (hs : 1 ≤ s) :
    (k : ℝ) ^ (-s) ≤ (1 : ℝ) / (k : ℝ) := by
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hmono : (k : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hk1
    linarith
  have hfin : (k : ℝ) ^ (-1 : ℝ) ≤ (1 : ℝ) / (k : ℝ) := by
    rw [Real.rpow_neg hkpos.le]
    rw [Real.rpow_one]
    rw [inv_eq_one_div]
  exact le_trans hmono hfin

/-- Power-weighted harmonic bound: for `s ≥ 1`, `Σ_{k ≤ A} k^(-s) ≤ 1 + log A`. -/
lemma sum_nat_rpow_neg_le_log (A : ℕ) (hA : 1 ≤ A) {s : ℝ} (hs : 1 ≤ s) :
    (∑ k ∈ Finset.Icc 1 A, (k : ℝ) ^ (-s)) ≤ 1 + Real.log (A : ℝ) := by
  have hle : (∑ k ∈ Finset.Icc 1 A, (k : ℝ) ^ (-s)) ≤
      (∑ k ∈ Finset.Icc 1 A, (1 : ℝ) / (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact nat_rpow_neg_le_one_div k (Finset.mem_Icc.mp hk).1 hs
  exact le_trans hle (Commons.Analysis.ExpLog.harmonic_le_one_add_log A hA)

/-- For naturals `Y < m` and real `t > 0`: `1 ≤ m^t / Y^t`. -/
lemma prod_gt_Y_rpow (Y m : ℕ) (hY : 1 ≤ Y) (hm : Y < m) {t : ℝ} (ht : 0 < t) :
    (1 : ℝ) ≤ (m : ℝ) ^ t / (Y : ℝ) ^ t := by
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hY)
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hYpos (by exact_mod_cast (Nat.le_of_lt hm))
  have hle : (Y : ℝ) ^ t ≤ (m : ℝ) ^ t :=
    Real.rpow_le_rpow hYpos.le (by exact_mod_cast (Nat.le_of_lt hm)) ht.le
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hYpos t)]
  simpa using hle

/-- If `Y < m` and `u v ≥ 0`, then `u v ≤ u v · m^t / Y^t` (used to insert the
decaying indicator factor into nonnegative pair terms). -/
lemma mul_le_mul_rpow_div (Y m : ℕ) (hY : 1 ≤ Y) (hm : Y < m) {t : ℝ} (ht : 0 < t)
    (uv : ℝ) (huv : 0 ≤ uv) : uv ≤ uv * (m : ℝ) ^ t / (Y : ℝ) ^ t := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) ^ t / (Y : ℝ) ^ t := prod_gt_Y_rpow Y m hY hm ht
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hY)
  calc
    uv = uv * 1 := by ring
    _ ≤ uv * ((m : ℝ) ^ t / (Y : ℝ) ^ t) := mul_le_mul_of_nonneg_left h1 huv
    _ = uv * (m : ℝ) ^ t / (Y : ℝ) ^ t := by ring

/-- `((a²·b³ : ℕ) : ℝ)^t = ((a:ℝ)^2)^t · ((b:ℝ)^3)^t` for real `t > 0` (naturals). -/
lemma cast_sq_mul_cube_rpow (a b : ℕ) {t : ℝ} (_ht : 0 < t) :
    (((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t) = (((a : ℝ) ^ 2) ^ t) * (((b : ℝ) ^ 3) ^ t) := by
  have hcast : (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  rw [hcast]
  have ha2 : 0 ≤ (a : ℝ) ^ 2 := by positivity
  have hb3 : 0 ≤ (b : ℝ) ^ 3 := by positivity
  rw [Real.mul_rpow ha2 hb3]

/-- Product factorization of a double sum: `Σ_a Σ_b (A a)·(B b) = (Σ A)·(Σ B)`. -/
lemma sum_double_prod {ι : Type*} (s : Finset ι) (A B : ι → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, A a * B b) = (∑ a ∈ s, A a) * (∑ b ∈ s, B b) := by
  calc
    (∑ a ∈ s, ∑ b ∈ s, A a * B b) = (∑ a ∈ s, A a * (∑ b ∈ s, B b)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]
    _ = (∑ a ∈ s, A a) * (∑ b ∈ s, B b) := by
      rw [← Finset.sum_mul]

/-- Pulling a constant (independent of both indices) out of a double sum. -/
lemma sum_double_mul_const {ι : Type*} (s : Finset ι) (f : ι → ι → ℝ) (c : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, f a b * c) = (∑ a ∈ s, ∑ b ∈ s, f a b) * c := by
  calc
    (∑ a ∈ s, ∑ b ∈ s, f a b * c) = (∑ a ∈ s, (∑ b ∈ s, f a b) * c) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_mul]
    _ = (∑ a ∈ s, ∑ b ∈ s, f a b) * c := by
      rw [← Finset.sum_mul]

/-- **Indicator-decay for the pair double sum.**  For nonnegative `u : ℕ → ℝ`,
`v : ℕ → ℝ` and real `t > 0`, the sum over pairs `a,b ∈ [1,Z]` satisfying
`Y < a²b³` of `u(a)v(b)` is at most the factored weighted sum divided by `Y^t`:
`(Σ_a u(a)(a²)^t)·(Σ_b v(b)(b³)^t) / Y^t`. -/
theorem pairWeight_tail_le (t : ℝ) (ht0 : 0 < t) (Y Z : ℕ) (hY : 1 ≤ Y)
    (u v : ℕ → ℝ) (hu : ∀ a : ℕ, 0 ≤ u a) (hv : ∀ b : ℕ, 0 ≤ v b) :
    (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then u a * v b else 0) ≤
      ((∑ a ∈ Finset.Icc 1 Z, u a * ((a : ℝ) ^ 2) ^ t) *
        (∑ b ∈ Finset.Icc 1 Z, v b * ((b : ℝ) ^ 3) ^ t)) / (Y : ℝ) ^ t := by
  classical
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hY)
  have hpt : ∀ a ∈ Finset.Icc 1 Z, ∀ b ∈ Finset.Icc 1 Z,
      (if Y < a ^ 2 * b ^ 3 then u a * v b else 0) ≤
        u a * v b * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t * (Y : ℝ) ^ (-t) := by
    intro a ha b hb
    by_cases hcond : Y < a ^ 2 * b ^ 3
    · have huv : 0 ≤ u a * v b := mul_nonneg (hu a) (hv b)
      have hbnd := mul_le_mul_rpow_div Y (a ^ 2 * b ^ 3) hY hcond ht0 (u a * v b) huv
      have heq : (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t / (Y : ℝ) ^ t =
          (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t * (Y : ℝ) ^ (-t) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hYpos)]
      rw [if_pos hcond]
      exact le_trans hbnd (le_of_eq heq)
    · have h1 : 0 ≤ (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t * (Y : ℝ) ^ (-t) := by
        have hm0 : 0 ≤ (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) := by positivity
        have hrp : 0 ≤ (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ^ t := Real.rpow_nonneg hm0 t
        have hYneg : 0 ≤ (Y : ℝ) ^ (-t) := Real.rpow_nonneg (le_of_lt hYpos) (-t)
        exact mul_nonneg (mul_nonneg (mul_nonneg (hu a) (hv b)) hrp) hYneg
      have hcast : (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) = (a : ℝ) ^ 2 * (b : ℝ) ^ 3 := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      simp [hcond]
      rw [← hcast]
      exact h1
  have hstep1 : (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then u a * v b else 0) ≤
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t * (Y : ℝ) ^ (-t)) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact hpt a ha b hb
  have hfac : (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t) =
      (∑ a ∈ Finset.Icc 1 Z, u a * ((a : ℝ) ^ 2) ^ t) *
        (∑ b ∈ Finset.Icc 1 Z, v b * ((b : ℝ) ^ 3) ^ t) := by
    calc
      (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
          (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t)
          = (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
              (u a * ((a : ℝ) ^ 2) ^ t) * (v b * ((b : ℝ) ^ 3) ^ t)) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [cast_sq_mul_cube_rpow a b ht0]
        ring
      _ = (∑ a ∈ Finset.Icc 1 Z, u a * ((a : ℝ) ^ 2) ^ t) *
          (∑ b ∈ Finset.Icc 1 Z, v b * ((b : ℝ) ^ 3) ^ t) := by
        rw [sum_double_prod]
  calc
    (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
        if Y < a ^ 2 * b ^ 3 then u a * v b else 0)
        ≤ (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
            (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t * (Y : ℝ) ^ (-t)) := hstep1
    _ = (∑ a ∈ Finset.Icc 1 Z, ∑ b ∈ Finset.Icc 1 Z,
            (u a * v b) * ((a ^ 2 * b ^ 3 : ℕ) : ℝ) ^ t) * (Y : ℝ) ^ (-t) := by
      rw [sum_double_mul_const]
    _ = ((∑ a ∈ Finset.Icc 1 Z, u a * ((a : ℝ) ^ 2) ^ t) *
          (∑ b ∈ Finset.Icc 1 Z, v b * ((b : ℝ) ^ 3) ^ t)) * (Y : ℝ) ^ (-t) := by
      rw [hfac]
    _ = ((∑ a ∈ Finset.Icc 1 Z, u a * ((a : ℝ) ^ 2) ^ t) *
          (∑ b ∈ Finset.Icc 1 Z, v b * ((b : ℝ) ^ 3) ^ t)) / (Y : ℝ) ^ t := by
      rw [Real.rpow_neg (le_of_lt hYpos)]
      rw [div_eq_mul_inv]

end Submission.Vdw
