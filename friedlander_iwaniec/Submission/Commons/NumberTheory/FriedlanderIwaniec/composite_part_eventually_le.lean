import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_natpairs

namespace Commons.NumberTheory.FriedlanderIwaniec

open Filter

/-- The number of representations of `n` as `a ^ 2 + b ^ 4` with `1 ≤ a`, `1 ≤ b`
is at most `Nat.sqrt (Nat.sqrt n) + 1`: the map `(a, b) ↦ b` is injective on the
solution set, and admissible `b` satisfy `b ^ 4 ≤ n`. -/
lemma rep_ncard_le_sqrt_sqrt (n : ℕ) :
    ({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n} : Set (ℕ × ℕ)).ncard
      ≤ Nat.sqrt (Nat.sqrt n) + 1 := by
  classical
  set S : Set (ℕ × ℕ) :=
    {p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n} with hS
  set T : Set ℕ := {b : ℕ | b ^ 4 ≤ n} with hT
  have hTfin : T.Finite := by
    apply Set.Finite.subset (s := (Finset.range (n + 1) : Set ℕ)) (Finset.finite_toSet _)
    intro b hb
    have hb4 : b ^ 4 ≤ n := hb
    rw [Finset.mem_coe, Finset.mem_range]
    rcases Nat.eq_zero_or_pos b with h | h
    · omega
    · have : b ≤ b ^ 4 := Nat.le_self_pow (by norm_num : 4 ≠ 0) b
      omega
  have hmem : ∀ p ∈ S, p.2 ∈ T := by
    intro p hp
    have hp' : 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n := hp
    show p.2 ^ 4 ≤ n
    calc p.2 ^ 4 ≤ p.1 ^ 2 + p.2 ^ 4 := Nat.le_add_left _ _
      _ = n := hp'.2.2
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) S := by
    intro p hp q hq heq
    have hp' : 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n := hp
    have hq' : 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 ^ 2 + q.2 ^ 4 = n := hq
    have heq' : p.2 = q.2 := heq
    have hsq : p.1 ^ 2 = q.1 ^ 2 := by
      have hh : p.1 ^ 2 + p.2 ^ 4 = q.1 ^ 2 + q.2 ^ 4 := by rw [hp'.2.2, hq'.2.2]
      rw [heq'] at hh
      exact Nat.add_right_cancel hh
    have h1 : p.1 = q.1 := by
      calc p.1 = Nat.sqrt (p.1 ^ 2) := (Nat.sqrt_eq' p.1).symm
        _ = Nat.sqrt (q.1 ^ 2) := by rw [hsq]
        _ = q.1 := Nat.sqrt_eq' q.1
    exact Prod.ext h1 heq'
  have hle := Set.ncard_le_ncard_of_injOn (fun p : ℕ × ℕ => p.2) hmem hinj hTfin
  have hTeq : T = {b : ℕ | b < Nat.sqrt (Nat.sqrt n) + 1} := by
    ext b; rw [hT]; exact pow_four_le_iff_lt_sqrt_sqrt_succ
  have hTcard : T.ncard = Nat.sqrt (Nat.sqrt n) + 1 := by
    rw [hTeq]
    rw [show ({b : ℕ | b < Nat.sqrt (Nat.sqrt n) + 1} : Set ℕ)
        = (Finset.range (Nat.sqrt (Nat.sqrt n) + 1) : Set ℕ) from by
      ext b; simp]
    rw [Set.ncard_coe_finset, Finset.card_range]
  rw [hTcard] at hle
  exact hle

/-- `Nat.sqrt (Nat.sqrt x)` (the integer fourth root of `x`) is bounded above by
the real fourth root `x ^ (1/4)`. -/
lemma sqrt_sqrt_cast_le_rpow (x : ℕ) :
    ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
  set n : ℕ := Nat.sqrt (Nat.sqrt x) with hn
  have h4 : n ^ 4 ≤ x := by
    have h1 : Nat.sqrt (Nat.sqrt x) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
    have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
    calc n ^ 4 = (Nat.sqrt (Nat.sqrt x) ^ 2) ^ 2 := by rw [hn]; ring
      _ ≤ (Nat.sqrt x) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ x := h2
  have h4R : (n : ℝ) ^ 4 ≤ (x : ℝ) := by exact_mod_cast h4
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hstep := Real.rpow_le_rpow (show (0:ℝ) ≤ (n:ℝ)^4 by positivity) h4R
    (show (0:ℝ) ≤ (1/4:ℝ) by norm_num)
  have heq : ((n:ℝ)^4) ^ (1/4:ℝ) = (n:ℝ) := by
    rw [← Real.rpow_natCast (n:ℝ) 4, ← Real.rpow_mul hnn]
    rw [show ((4:ℕ):ℝ) * (1/4:ℝ) = 1 by norm_num, Real.rpow_one]
  rw [heq] at hstep
  exact hstep

/-- The sum of `Λ` over the non-prime `n ≤ x` is `ψ x - θ x`. -/
lemma sum_vonMangoldt_notPrime_eq (x : ℕ) :
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n)
      = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
  classical
  have hIcc : Finset.Icc 0 x = Finset.range (x + 1) := by
    ext n; simp [Finset.mem_Icc, Finset.mem_range]
  have hpsi : Chebyshev.psi (x : ℝ)
      = ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, hIcc]
  have htheta : Chebyshev.theta (x : ℝ)
      = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => n.Prime),
          ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, hIcc]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hpn : n.Prime := (Finset.mem_filter.mp hn).2
    exact (ArithmeticFunction.vonMangoldt_apply_prime hpn).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (x + 1))
    (p := fun n : ℕ => n.Prime)
    (f := fun n : ℕ => ArithmeticFunction.vonMangoldt n)
  have this : (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n)
      = (∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n)
        - (∑ n ∈ (Finset.range (x + 1)).filter (fun n => n.Prime),
            ArithmeticFunction.vonMangoldt n) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit
  rw [this, ← hpsi, ← htheta]

/-- Pointwise bound on the sum in the target statement. -/
lemma composite_sum_le (x : ℕ) :
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n *
          (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
      ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  classical
  have hterm : ∀ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n *
          (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ)
        ≤ ArithmeticFunction.vonMangoldt n * ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) := by
    intro n hn
    have hnx : n ≤ x := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      omega
    have hrep : (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ)
        ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) := by
      have h1 := rep_ncard_le_sqrt_sqrt n
      have h2 : Nat.sqrt (Nat.sqrt n) + 1 ≤ Nat.sqrt (Nat.sqrt x) + 1 :=
        Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hnx)) 1
      exact_mod_cast (le_trans h1 h2)
    exact mul_le_mul_of_nonneg_left hrep ArithmeticFunction.vonMangoldt_nonneg
  calc (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n *
          (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
      ≤ ∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n * ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n)) * ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) :=
        (Finset.sum_mul _ _ _).symm
    _ = ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
        rw [sum_vonMangoldt_notPrime_eq]; ring

/-- For large `x`, `(⁴√x + 1) · 1.099 √x ≤ 1.1 x^{3/4}`. -/
lemma numeric_eventually :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) * (1.099 * Real.sqrt x)
        ≤ 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := by
  rw [Filter.eventually_atTop]
  refine ⟨1099 ^ 4, fun x hx => ?_⟩
  have hx1 : (1 : ℕ) ≤ x := le_trans (by norm_num) hx
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hx1)
  set t : ℝ := (x : ℝ) ^ (1 / 4 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hxR.le _
  have ht4 : t ^ 4 = (x : ℝ) := by
    rw [ht, ← Real.rpow_natCast ((x : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hxR.le]
    norm_num
  have ht1099 : 1099 ≤ t := by
    have h4le : ((1099 : ℝ)) ^ 4 ≤ t ^ 4 := by
      rw [ht4]
      have hcast : ((1099 : ℕ) : ℝ) ^ 4 ≤ (x : ℝ) := by exact_mod_cast hx
      simpa using hcast
    exact (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ 1099 by norm_num) ht0
      (by norm_num : (4 : ℕ) ≠ 0)).mp h4le
  have hcast : ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) ≤ t + 1 := by
    have h := sqrt_sqrt_cast_le_rpow x
    rw [← ht] at h
    push_cast
    linarith
  have hkey : 1.099 * (t + 1) ≤ 1.1 * t := by nlinarith [ht1099]
  have ht2sqrt : t ^ 2 = Real.sqrt (x : ℝ) := by
    rw [ht, ← Real.rpow_natCast ((x : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hxR.le,
      show (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  have ht3 : t ^ 3 = (x : ℝ) ^ (3 / 4 : ℝ) := by
    rw [ht, ← Real.rpow_natCast ((x : ℝ) ^ (1 / 4 : ℝ)) 3, ← Real.rpow_mul hxR.le,
      show (1 / 4 : ℝ) * (3 : ℕ) = 3 / 4 by norm_num]
  have ht2nn : 0 ≤ t ^ 2 := sq_nonneg t
  have hmain : 1.099 * (t + 1) * t ^ 2 ≤ 1.1 * t ^ 3 := by
    have := mul_le_mul_of_nonneg_right hkey ht2nn
    nlinarith [this]
  calc ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) * (1.099 * Real.sqrt x)
      = ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) * (1.099 * t ^ 2) := by rw [ht2sqrt]
    _ ≤ (t + 1) * (1.099 * t ^ 2) :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = 1.099 * (t + 1) * t ^ 2 := by ring
    _ ≤ 1.1 * t ^ 3 := hmain
    _ = 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := by rw [ht3]

lemma composite_part_eventually_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n *
            (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
        ≤ 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := by
  filter_upwards [Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le,
    numeric_eventually] with x hpsi hnum
  have hc_nonneg : 0 ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) := by positivity
  calc (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime),
          ArithmeticFunction.vonMangoldt n *
            (({p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 4 = n}.ncard : ℕ) : ℝ))
      ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := composite_sum_le x
    _ ≤ ((Nat.sqrt (Nat.sqrt x) + 1 : ℕ) : ℝ) * (1.099 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hpsi hc_nonneg
    _ ≤ 1.1 * (x : ℝ) ^ (3 / 4 : ℝ) := hnum

end Commons.NumberTheory.FriedlanderIwaniec
