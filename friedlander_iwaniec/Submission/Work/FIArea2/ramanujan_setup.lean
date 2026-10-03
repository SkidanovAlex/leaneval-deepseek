import Mathlib

namespace Work.FIArea2

open scoped BigOperators
open Finset

/-!
# The classical bound for the Ramanujan sum

`R(h;b) = ∑_{1 ≤ η ≤ b, (η,b)=1} e(ηh/b)`, `e(x) = exp(2πix)`, satisfies `‖R(h;b)‖ ≤ (h,b)`.

This is the input to Lemma 8.1 of Friedlander–Iwaniec ((8.5)), the Ramanujan sum appearing
in (8.3).

The proof route implemented here is:

* `E x = exp (2πix)` and the classical vanishing sum `T N m = ∑_{j=1}^N E(jm/N) = N [N ∣ m]`;
* Möbius inversion over the coprimality condition, which evaluates the Ramanujan sum as
  `R(h;b) = ∑_{d ∣ b} μ(d) · (b/d) · [b/d ∣ h]`, i.e. exhibits it as the value at `b` of the
  arithmetic function `μ * (n ↦ n·[n ∣ h])`;
* multiplicativity of that arithmetic function and the evaluation on prime powers, where
  `|R(h;p^a)| ≤ p^{min(a,v_p(h))}`;
* `Nat.multiplicative_factorization`, which turns both the value and `gcd(b,h)` into products
  over the prime factorization of `b`.
-/

/-- The additive character `E x = exp (2πix)` restricted to the reals. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_zero : E 0 = 1 := by
  unfold E
  simp

lemma E_int (n : ℤ) : E (n : ℝ) = 1 := by
  unfold E
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑(n : ℝ)
      = (n : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma E_pow (x : ℝ) (N : ℕ) : E x ^ N = E (N * x) := by
  unfold E
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma E_norm (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
        push_cast; ring]
  rw [Complex.norm_exp_ofReal_mul_I]

lemma E_one_iff (x : ℝ) : E x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold E
  rw [Complex.exp_eq_one_iff]
  have h2 : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [mul_comm (↑n : ℂ) (2 * ↑Real.pi * Complex.I)] at hn
    have : (↑x : ℂ) = ↑n := mul_left_cancel₀ h2 hn
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- The summand of the Ramanujan sum, in `E`-notation: `E (η h / b)`. -/
lemma E_mul_div (m : ℤ) (j N : ℕ) :
    E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ)) = (E ((m : ℝ) / (N : ℝ))) ^ j := by
  induction j with
  | zero => simp [E]
  | succ k ih =>
    have hstep : (((m * ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) / (N : ℝ))
        = (((m * (k : ℤ) : ℤ) : ℝ) / (N : ℝ)) + (m : ℝ) / (N : ℝ) := by
      push_cast; ring
    rw [hstep, E_add, ih]
    ring

lemma E_div_exp (X : ℝ) (b : ℕ) :
    E (X / (b : ℝ)) = Complex.exp (2 * Real.pi * Complex.I * X / (b : ℝ)) := by
  unfold E
  rw [Complex.ofReal_div]
  rw [mul_div_assoc]

/-- The exponential sum `T N m = ∑_{j=1}^N E (j m / N)`; its classical value is `N [N ∣ m]`. -/
noncomputable def T (N : ℕ) (m : ℤ) : ℂ :=
  ∑ j ∈ Icc 1 N, E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ))

/-- **Vanishing of the incomplete geometric sum**: `∑_{j=1}^{N} e(jm/N) = N` if `N ∣ m`,
and `0` otherwise. -/
lemma T_eq (N : ℕ) (hN : 1 ≤ N) (m : ℤ) :
    T N m = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  unfold T
  set z : ℂ := E ((m : ℝ) / (N : ℝ)) with hz
  have hterm : ∀ j ∈ Icc 1 N, E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ)) = z ^ j := by
    intro j _; rw [hz, E_mul_div]
  have h1 : (∑ j ∈ Icc 1 N, E (((m * (j : ℤ) : ℤ) : ℝ) / (N : ℝ))) = ∑ j ∈ Icc 1 N, z ^ j :=
    sum_congr rfl hterm
  rw [h1]
  have hIcc : Icc 1 N = Ico 1 (N + 1) := by ext x; simp
  rw [hIcc, sum_Ico_eq_sum_range, show N + 1 - 1 = N from by omega]
  have hpowsum : ∑ k ∈ range N, z ^ (1 + k) = z * ∑ k ∈ range N, z ^ k := by
    rw [Finset.mul_sum]
    apply sum_congr rfl; intro k _; rw [pow_add, pow_one]
  rw [hpowsum]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hzN : z ^ N = 1 := by
    rw [hz, E_pow, show (N : ℝ) * ((m : ℝ) / (N : ℝ)) = (m : ℝ) by field_simp]
    exact E_int m
  have hdiv : (N : ℤ) ∣ m ↔ z = 1 := by
    rw [hz, E_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]; push_cast; field_simp
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk2 : (m : ℝ) = (k : ℝ) * (N : ℝ) := by
        rw [div_eq_iff hN0] at hk; exact hk
      have : m = k * (N : ℤ) := by exact_mod_cast hk2
      rw [this]; ring
  by_cases h : (N : ℤ) ∣ m
  · rw [if_pos h, (hdiv.mp h)]
    simp
  · rw [if_neg h]
    have hz1 : z ≠ 1 := fun hh => h (hdiv.mpr hh)
    rw [geom_sum_eq hz1, hzN]
    simp

/-- **Möbius inversion of the coprimality indicator**: `[(n,η) = 1] = ∑_{d ∣ n, d ∣ η} μ(d)`. -/
lemma moebius_indicator (n η : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
      = if Nat.Coprime n η then 1 else 0 := by
  rw [← sum_filter]
  have hf : n.divisors.filter (fun m => m ∣ η) = (Nat.gcd n η).divisors := by
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.gcd_dvd_left n η)]
    apply filter_congr
    intro m hm
    rw [Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨Nat.dvd_of_mem_divisors hm, h⟩, fun h => h.2⟩
  rw [hf]
  have h2 : (∑ d ∈ (Nat.gcd n η).divisors, ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) d))
      = if Nat.gcd n η = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply
          (f := (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) (x := Nat.gcd n η),
        ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  exact h2

/-- Reindexing a divisor-restricted sum: `∑_{d ∣ η ≤ n} f η = ∑_{j ≤ n/d} f (dj)`. -/
lemma sum_Icc_filter_dvd (n d : ℕ) (hd : d ∣ n) (f : ℕ → ℂ) :
    ∑ η ∈ (Icc 1 n).filter (fun η => d ∣ η), f η = ∑ j ∈ Icc 1 (n / d), f (d * j) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · obtain rfl : n = 0 := Nat.zero_dvd.mp hd
    simp
  refine Finset.sum_bij' (fun η _ => η / d) (fun j _ => d * j) ?_ ?_ ?_ ?_ ?_
  · intro η hη
    simp only [mem_filter, mem_Icc] at hη
    obtain ⟨⟨h1, h2⟩, h3⟩ := hη
    simp only [mem_Icc]
    refine ⟨?_, Nat.div_le_div_right h2⟩
    rw [Nat.le_div_iff_mul_le hdpos, one_mul]
    exact Nat.le_of_dvd (by omega) h3
  · intro j hj
    simp only [mem_Icc] at hj
    obtain ⟨h1, h2⟩ := hj
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d j⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hdpos (by omega))
    · calc d * j ≤ d * (n / d) := Nat.mul_le_mul_left d h2
        _ = n / d * d := by ring
        _ ≤ n := Nat.div_mul_le_self n d
  · intro η hη
    simp only [mem_filter, mem_Icc] at hη
    exact Nat.mul_div_cancel' hη.2
  · intro j hj
    simp only [mem_Icc] at hj
    exact Nat.mul_div_cancel_left j hdpos
  · intro η hη
    simp only [mem_filter, mem_Icc] at hη
    rw [Nat.mul_div_cancel' hη.2]

/-- The Ramanujan sum `R(b;m) = ∑_{η ≤ b, (η,b)=1} e(ηm/b)`. -/
noncomputable def ram (b : ℕ) (m : ℤ) : ℂ :=
  ∑ η ∈ (Icc 1 b).filter (fun η => Nat.Coprime η b),
    E (((m * (η : ℤ) : ℤ) : ℝ) / (b : ℝ))

/-- The Ramanujan sum evaluated by Möbius inversion:
`R(b;m) = ∑_{d ∣ b} μ(d) · (b/d) · [b/d ∣ m]`. -/
lemma ram_eq_moebius (n : ℕ) (hn : 1 ≤ n) (m : ℤ) :
    ram n m = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℂ) *
        (if ((n / d : ℕ) : ℤ) ∣ m then ((n / d : ℕ) : ℂ) else 0) := by
  have hn0 : n ≠ 0 := by omega
  have hstep1 : ram n m
      = ∑ η ∈ Icc 1 n, (if Nat.Coprime η n then E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) else 0) := by
    unfold ram
    rw [sum_filter]
  rw [hstep1]
  have hstep2 : ∀ η : ℕ, (if Nat.Coprime η n then E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) else 0)
      = (∑ d ∈ n.divisors, if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) := by
    intro η
    rw [moebius_indicator n η hn0]
    by_cases h : Nat.Coprime η n
    · rw [if_pos h, if_pos h.symm, one_mul]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
  have hstep2' : (∑ η ∈ Icc 1 n, (if Nat.Coprime η n then E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) else 0))
      = ∑ η ∈ Icc 1 n, (∑ d ∈ n.divisors, if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) :=
    sum_congr rfl (fun η _ => hstep2 η)
  rw [hstep2']
  have hstep3 : (∑ η ∈ Icc 1 n, (∑ d ∈ n.divisors, if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)))
      = ∑ d ∈ n.divisors, ∑ η ∈ Icc 1 n, (if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) := by
    have h : (∑ η ∈ Icc 1 n, (∑ d ∈ n.divisors, if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)))
        = ∑ η ∈ Icc 1 n, ∑ d ∈ n.divisors, (if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) := by
      apply sum_congr rfl; intro η _
      rw [Finset.sum_mul]
    rw [h, Finset.sum_comm]
  rw [hstep3]
  apply sum_congr rfl
  intro d hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hdpos
  have h1 : (∑ η ∈ Icc 1 n, (if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
        * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)))
      = ∑ η ∈ (Icc 1 n).filter (fun η => d ∣ η), (ArithmeticFunction.moebius d : ℂ)
        * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) := by
    have e : ∀ η : ℕ, (if d ∣ η then (ArithmeticFunction.moebius d : ℂ) else 0)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ))
        = (if d ∣ η then (ArithmeticFunction.moebius d : ℂ)
          * E (((m * (η : ℤ) : ℤ) : ℝ) / (n : ℝ)) else 0) := by
      intro η; by_cases h : d ∣ η <;> simp [h]
    rw [sum_congr rfl (fun η _ => e η), ← sum_filter]
  have h2 : (∑ j ∈ Icc 1 (n / d), E (((m * (↑(d * j) : ℤ) : ℤ) : ℝ) / (n : ℝ))) = T (n / d) m := by
    unfold T
    apply sum_congr rfl
    intro j _
    congr 1
    have hdr : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hnd0 : ((n / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n / d ≠ 0 by omega)
    push_cast
    rw [← hdr]
    field_simp
  rw [h1]
  rw [← Finset.mul_sum]
  rw [sum_Icc_filter_dvd n d hdn]
  rw [h2]
  rw [T_eq (n / d) hndpos m]

end Work.FIArea2
