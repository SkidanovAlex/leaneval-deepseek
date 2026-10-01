import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.ZeroDensity.Jutila.LzAux

open ArithmeticFunction

noncomputable section

/-- `d₀(n) = 1/(n·κ(n))`, packaged as an arithmetic function. -/
def d0 : ArithmeticFunction ℝ := ⟨fun n => 1/((n:ℝ) * kap n), by simp⟩

@[simp] lemma d0_apply (n : ℕ) : d0 n = 1/((n:ℝ) * kap n) := rfl

/-- The arithmetic function `n ↦ μ(n)/n`. -/
def g : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ)/n, by simp⟩

@[simp] lemma g_apply (n : ℕ) : g n = (ArithmeticFunction.moebius n : ℝ)/n := rfl

/-- The arithmetic function `n ↦ μ(n)/κ(n)`. -/
def k : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ)/kap n, by simp⟩

@[simp] lemma k_apply (n : ℕ) : k n = (ArithmeticFunction.moebius n : ℝ)/kap n := rfl

/-! ## Values of `κ` -/

lemma kap_one : kap 1 = 1 := by
  unfold kap; rw [Nat.primeFactors_one, Finset.prod_empty]

lemma kap_prime {p : ℕ} (hp : p.Prime) : kap p = (p:ℝ)+1 := by
  unfold kap; rw [hp.primeFactors, Finset.prod_singleton]

lemma kap_prime_pow {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) : kap (p^j) = (p:ℝ)+1 := by
  unfold kap; rw [Nat.primeFactors_prime_pow hj hp, Finset.prod_singleton]

/-! ## Values of `d0`, `g`, `k` -/

lemma d0_one : d0 1 = 1 := by rw [d0_apply, kap_one]; norm_num

lemma d0_prime {p : ℕ} (hp : p.Prime) : d0 p = 1/((p:ℝ)*((p:ℝ)+1)) := by
  rw [d0_apply, kap_prime hp]

lemma d0_prime_pow {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    d0 (p^j) = 1/((p:ℝ)^j * ((p:ℝ)+1)) := by
  rw [d0_apply, kap_prime_pow hp (by omega)]; push_cast; ring

lemma g_one : g 1 = 1 := by rw [g_apply, ArithmeticFunction.moebius_apply_one]; norm_num

lemma g_prime {p : ℕ} (hp : p.Prime) : g p = -1/(p:ℝ) := by
  rw [g_apply, ArithmeticFunction.moebius_apply_prime hp]; simp

lemma g_prime_pow_zero {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) : g (p^j) = 0 := by
  rw [g_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  simp

lemma k_one : k 1 = 1 := by rw [k_apply, ArithmeticFunction.moebius_apply_one, kap_one]; norm_num

lemma k_prime {p : ℕ} (hp : p.Prime) : k p = -1/((p:ℝ)+1) := by
  rw [k_apply, ArithmeticFunction.moebius_apply_prime hp, kap_prime hp]; simp

lemma k_prime_pow_zero {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) : k (p^j) = 0 := by
  rw [k_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
  simp

/-! ## Multiplicativity -/

lemma d0_mul : d0.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [d0_apply, kap_one]; norm_num, ?_⟩
  intro m n hm hn hcop
  rw [d0_apply, d0_apply, d0_apply, kap_mul_of_coprime hcop]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hkm : kap m ≠ 0 := kap_ne_zero m
  have hkn : kap n ≠ 0 := kap_ne_zero n
  push_cast
  field_simp

lemma g_mul : g.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [g_apply, ArithmeticFunction.moebius_apply_one]; norm_num, ?_⟩
  intro m n hm hn hcop
  rw [g_apply, g_apply, g_apply]
  have hmu : (ArithmeticFunction.moebius (m * n) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]; push_cast; ring
  rw [hmu]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

lemma k_mul : k.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [k_apply, ArithmeticFunction.moebius_apply_one, kap_one]; norm_num, ?_⟩
  intro m n hm hn hcop
  rw [k_apply, k_apply, k_apply, kap_mul_of_coprime hcop]
  have hmu : (ArithmeticFunction.moebius (m * n) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]; push_cast; ring
  rw [hmu]
  have hkm : kap m ≠ 0 := kap_ne_zero m
  have hkn : kap n ≠ 0 := kap_ne_zero n
  field_simp

/-! ## Evaluation at prime powers -/

/-- Convolution at a prime power, before the individual values are inserted: only the two
divisors `p^(i-1)` and `p^i` contribute. -/
lemma conv_prime_pow_succ (p : ℕ) (hp : p.Prime) (i : ℕ) :
    (d0 * g) (p^(i+1)) = d0 (p^i) * g p + d0 (p^(i+1)) * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => d0 a * g b),
      Nat.sum_divisors_prime_pow hp]
  have hgoal : (∑ x ∈ Finset.range (i+1+1), d0 (p^x) * g (p^(i+1) / p^x))
      = (∑ x ∈ Finset.range (i+1+1), d0 (p^x) * g (p^(i+1-x))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Nat.pow_div (by omega) hp.pos]
  rw [hgoal]
  have hsub : ({i, i+1} : Finset ℕ) ⊆ Finset.range (i+1+1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    rcases hx with rfl | rfl <;> omega
  have hzero : ∀ x ∈ Finset.range (i+1+1), x ∉ ({i, i+1} : Finset ℕ) →
      d0 (p^x) * g (p^(i+1-x)) = 0 := by
    intro x hx hxs
    rw [Finset.mem_range] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxs
    obtain ⟨hxi, hxi1⟩ := hxs
    have hle : 2 ≤ i + 1 - x := by omega
    rw [g_prime_pow_zero hp hle, mul_zero]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega)]
  simp

/-- The two arithmetic functions `d0 * g` and `k` agree at every prime power. -/
lemma prime_pow_key (p : ℕ) (hp : p.Prime) : ∀ i, (d0 * g) (p^i) = k (p^i)
  | 0 => by rw [pow_zero, ArithmeticFunction.mul_apply_one, d0_one, g_one, k_one]; norm_num
  | (i+1) => by
      rcases i with _ | i
      · simp only [Nat.zero_add, pow_one]
        have h := conv_prime_pow_succ p hp 0
        simp only [Nat.zero_add, pow_zero, pow_one] at h
        rw [h, d0_one, d0_prime hp, g_prime hp, g_one, k_prime hp]
        have hp0 : (p:ℝ) ≠ 0 := by
          have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          exact ne_of_gt this
        have hp1 : ((p:ℝ)+1) ≠ 0 := by
          have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          linarith
        field_simp
        ring
      · have h := conv_prime_pow_succ p hp (i+1)
        have h1 : d0 (p^(i+1)) = 1/((p:ℝ)^(i+1) * ((p:ℝ)+1)) := d0_prime_pow hp (by omega)
        have h2 : d0 (p^((i+1)+1)) = 1/((p:ℝ)^((i+1)+1) * ((p:ℝ)+1)) :=
          d0_prime_pow hp (by omega)
        have h3 : k (p^((i+1)+1)) = 0 := k_prime_pow_zero hp (by omega)
        have h4 : (p:ℝ)^((i+1)+1) = (p:ℝ)^(i+1) * (p:ℝ) := by rw [pow_succ]
        rw [h, h1, h2, g_prime hp, g_one, h3, h4]
        have hp0 : (p:ℝ) ≠ 0 := by
          have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          exact ne_of_gt this
        have hp1 : ((p:ℝ)+1) ≠ 0 := by
          have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
          linarith
        have hpi : (p:ℝ)^(i+1) ≠ 0 := pow_ne_zero (i+1) hp0
        field_simp
        ring

/-- **Dirichlet-convolution identity for `μ/κ`.** For every `n ≥ 1`, `Σ_{d|n} (1/(d·κ(d)))·(μ(n/d)/(n/d)) = μ(n)/κ(n)` where `κ(d) = ∏_{p|d}(p+1) = Work.ZeroDensity.Jutila.kap d`. Equivalently `μ/κ = d₀ ∗ (μ/id)` with `d₀(d) = 1/(d·κ(d))`. Route: both sides are multiplicative; package `d₀` and `m ↦ μ(m)/m` as `ArithmeticFunction ℝ`, use `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`, and evaluate at `p^i` with `ArithmeticFunction.mul_apply`, `Nat.sum_divisorsAntidiagonal`, `Nat.sum_divisors_prime_pow`: the terms with `p^i/d ∉ {1,p}` vanish, giving `1/(p^i(p+1)) + 1/(p^{i−1}(p+1))·(−1/p) = 0` for `i ≥ 2` and `1/(p(p+1)) − 1/p = −1/(p+1)` for `i = 1`, matching `μ(p^i)/κ(p^i)`. (`d₀` is multiplicative by `kap_mul_of_coprime`.) -/
theorem KappaConvIdentity :
    ∀ (n : ℕ), 1 ≤ n →
      (∑ d ∈ n.divisors,
          (1 / ((d : ℝ) * Work.ZeroDensity.Jutila.kap d))
            * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)))
        = (ArithmeticFunction.moebius n : ℝ) / Work.ZeroDensity.Jutila.kap n := by
  intro n _
  have hfun : d0 * g = k :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (d0 * g)
      (ArithmeticFunction.IsMultiplicative.mul d0_mul g_mul) k k_mul).mpr
      (fun p i hp => prime_pow_key p hp i)
  have h2 : (d0 * g) n
      = ∑ d ∈ n.divisors,
          (1 / ((d : ℝ) * kap d))
            * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => d0 a * g b)]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [d0_apply, g_apply]
  rw [← h2, hfun]
  exact k_apply n

end

end Work.ZeroDensity.Jutila.LzAux
