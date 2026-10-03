import Mathlib
import Submission.Work.FIArea7.Classical172Defs

namespace Work.FIArea7

/-- **Finset plumbing.**  A double sum of complex numbers, each term of which is bounded
pointwise by `A a · B b · P`, is at most `P` times the product of the two sums `∑ A`, `∑ B`. -/
private lemma t2psi_S2_double_sum_aux
    (P : ℝ) (A B : ℕ → ℝ) (Y : ℕ) (M : ℕ → ℕ → ℂ)
    (hM : ∀ a ∈ Finset.Icc 1 Y, ∀ b ∈ Finset.Icc 1 Y, ‖M a b‖ ≤ A a * B b * P) :
    ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, M a b‖
      ≤ P * (∑ a ∈ Finset.Icc 1 Y, A a) * (∑ b ∈ Finset.Icc 1 Y, B b) := by
  calc ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, M a b‖
      ≤ ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, ‖M a b‖ := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
    _ ≤ ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y, A a * B b * P :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hM a ha b hb))
    _ = P * (∑ a ∈ Finset.Icc 1 Y, A a) * (∑ b ∈ Finset.Icc 1 Y, B b) := by
        have h1 : ∀ a, (∑ b ∈ Finset.Icc 1 Y, A a * B b * P)
            = (A a * (∑ b ∈ Finset.Icc 1 Y, B b)) * P := fun a => by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- **Pointwise term bound for the `S₂` double sum.**  With `T(a,b) = ∑_{m ≤ N/(ab)} λ(cc·(ab)·m)`
the inner `m`-sum of the second Vaughan term, the single summand `μ(a)·Λ(b)·T(a,b)` is bounded by
the two filtered weights times the constant, using `|μ(a)| ≤ 1`, `Λ(b) ≥ 0`, and the fact that
`a·b > N` forces `T(a,b) = 0`. -/
private lemma t2psi_S2_term_le_aux
    (N cc d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (C3 : ℝ) (a b : ℕ)
    (hC3 : 0 ≤ C3) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpt : a * b ≤ N →
        ‖∑ m ∈ Finset.Icc 1 (N / (a * b)),
            Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))‖
          ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
              * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
              * ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
              * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4))) :
    ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / (a * b)),
          Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))‖
      ≤ (if a ≤ N then ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)) else 0)
          * (if b ≤ N then ArithmeticFunction.vonMangoldt b
              * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) else 0)
          * (C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
              * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)) := by
  let T : ℂ := ∑ m ∈ Finset.Icc 1 (N / (a * b)),
      Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))
  let P : ℝ := C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4
      * Real.sqrt cc * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
  let fa : ℝ := (((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)
  let gb : ℝ := (((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)
  have hpt' : a * b ≤ N → ‖T‖ ≤ P * fa * gb := hpt
  change ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖
      ≤ (if a ≤ N then fa else 0)
          * (if b ≤ N then ArithmeticFunction.vonMangoldt b * gb else 0) * P
  have hTzero : ∀ h : N < a * b, T = 0 := by
    intro h
    show (∑ m ∈ Finset.Icc 1 (N / (a * b)),
        Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))) = 0
    rw [Nat.div_eq_of_lt h, Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num)]
    simp
  have hPnn : 0 ≤ P := by
    change 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4
      * Real.sqrt cc * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
    have hlog : 0 ≤ Real.log ((cc : ℝ) * (N : ℝ) + 2) := by
      apply Real.log_nonneg
      have h0 : (0 : ℝ) ≤ (cc : ℝ) * (N : ℝ) := by positivity
      linarith
    have h1 : 0 ≤ C3 * (d : ℝ) := mul_nonneg hC3 (by positivity)
    have h2 : 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) := mul_nonneg h1 (by positivity)
    have h3 : 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 :=
      mul_nonneg h2 (by positivity)
    have h4 : 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4
        * Real.sqrt cc := mul_nonneg h3 (Real.sqrt_nonneg (cc : ℝ))
    have h5 : 0 ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4
        * Real.sqrt cc * (N : ℝ) ^ ((3:ℝ)/4) :=
      mul_nonneg h4 (Real.rpow_nonneg (by positivity) ((3:ℝ)/4))
    exact mul_nonneg h5 hlog
  have hfa : 0 ≤ fa := by
    change 0 ≤ (((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hgb : 0 ≤ gb := by
    change 0 ≤ (((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hLb : 0 ≤ ArithmeticFunction.vonMangoldt b := ArithmeticFunction.vonMangoldt_nonneg
  have hmu : ‖(ArithmeticFunction.moebius a : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
  have hLbn : ‖(((ArithmeticFunction.vonMangoldt b : ℝ)) : ℂ)‖ = ArithmeticFunction.vonMangoldt b := by
    simp [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hM_le : ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖
      ≤ ArithmeticFunction.vonMangoldt b * ‖T‖ := by
    rw [norm_mul, norm_mul, hLbn]
    calc (‖(ArithmeticFunction.moebius a : ℂ)‖ * ArithmeticFunction.vonMangoldt b) * ‖T‖
        ≤ (1 * ArithmeticFunction.vonMangoldt b) * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu hLb) (norm_nonneg T)
      _ = ArithmeticFunction.vonMangoldt b * ‖T‖ := by ring
  by_cases h1 : a ≤ N
  · by_cases h2 : b ≤ N
    · rw [if_pos h1, if_pos h2]
      by_cases hab : a * b ≤ N
      · calc ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖
            ≤ ArithmeticFunction.vonMangoldt b * ‖T‖ := hM_le
          _ ≤ ArithmeticFunction.vonMangoldt b * (P * fa * gb) :=
                mul_le_mul_of_nonneg_left (hpt' hab) hLb
          _ = fa * (ArithmeticFunction.vonMangoldt b * gb) * P := by ring
      · have hL : ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖ = 0 := by
          rw [hTzero (Nat.lt_of_not_le hab), mul_zero, norm_zero]
        rw [hL]
        exact mul_nonneg (mul_nonneg hfa (mul_nonneg hLb hgb)) hPnn
    · rw [if_pos h1, if_neg h2, mul_zero, zero_mul]
      have hlt : N < a * b := by
        have hb' : N < b := Nat.lt_of_not_le h2
        have hle : b ≤ a * b := by
          calc b = 1 * b := (one_mul b).symm
            _ ≤ a * b := Nat.mul_le_mul_right b ha
        omega
      have hL : ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖ = 0 := by
        rw [hTzero hlt, mul_zero, norm_zero]
      rw [hL]
  · rw [if_neg h1, zero_mul, zero_mul]
    have hlt : N < a * b := by
      have ha' : N < a := Nat.lt_of_not_le h1
      have hle : a ≤ a * b := by
        calc a = a * 1 := (mul_one a).symm
          _ ≤ a * b := Nat.mul_le_mul_left a hb
      omega
    have hL : ‖(ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * T‖ = 0 := by
      rw [hTzero hlt, mul_zero, norm_zero]
    rw [hL]

/-- **Finset plumbing for `S₂`.**  If the inner `m`-sum satisfies the pointwise bound `hpt`, then
the whole double sum of the second Vaughan term is at most
`C3 · d · (|k|+1) · τ(cc)^4 · √cc · N^{3/4} · log(cc·N+2)` times the two filtered sums
`∑_{a ≤ Y, a ≤ N} τ(a)^4 a^{-1/4}` and `∑_{b ≤ Y, b ≤ N} Λ(b) τ(b)^4 b^{-1/4}`.
Every pair with `a·b > N` contributes `0` (the inner range `Icc 1 (N/(ab))` is empty), and for the
remaining pairs `a, b ≤ N`, so the indicators `1_{a ≤ N}`, `1_{b ≤ N}` may be inserted. -/
theorem t2psi_S2_double_sum_le
    (N cc d Y : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (C3 : ℝ)
    (hC3 : 0 ≤ C3) (hN : 1 ≤ N) (hc : 1 ≤ cc)
    (hpt : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a * b ≤ N →
        ‖∑ m ∈ Finset.Icc 1 (N / (a * b)),
            Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))‖
          ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
              * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
              * ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
              * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4))) :
    ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
          ∑ m ∈ Finset.Icc 1 (N / (a * b)),
            Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))‖
      ≤ C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
          * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
          * (∑ a ∈ Finset.Icc 1 Y,
              if a ≤ N then ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)) else 0)
          * (∑ b ∈ Finset.Icc 1 Y,
              if b ≤ N then ArithmeticFunction.vonMangoldt b
                * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) else 0) := by
  let P : ℝ := C3 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4
      * Real.sqrt cc * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
  let A : ℕ → ℝ := fun a =>
      if a ≤ N then ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4)) else 0
  let B : ℕ → ℝ := fun b =>
      if b ≤ N then ArithmeticFunction.vonMangoldt b
        * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) else 0
  let M : ℕ → ℕ → ℂ := fun a b =>
      (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / (a * b)),
          Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))
  refine t2psi_S2_double_sum_aux P A B Y M ?_
  intro a ha b hb
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
  exact t2psi_S2_term_le_aux N cc d k chi C3 a b hC3 ha1 hb1 (hpt a b ha1 hb1)

end Work.FIArea7
