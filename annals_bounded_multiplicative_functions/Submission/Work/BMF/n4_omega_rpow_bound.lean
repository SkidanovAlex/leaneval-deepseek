import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `(2m)^{ω(q)}` is sub-polynomial in `q`

For every `ℓ, m ≥ 1` there is `q₀` such that for all `q ≥ q₀`
  `(2m)^{ω(q)} ≤ q^{1/(2ℓ)}`,
where `ω(q) = q.primeFactors.card` is the number of distinct prime factors of `q`.

Equivalently: `ω(q) = o(log q)`, i.e. for every `c > 0` one has `ω(q) ≤ c log q` for all
sufficiently large `q`.  The proof is the classical one:

* `∏_{p ∣ n} p` divides `n`, hence is `≤ n`;
* the `k = ω(n)` primes dividing `n` are distinct integers `≥ 2`, so their product is at least
  the product of the `k` smallest such integers, namely `(k+1)!`
  (`prod_ge_factorial_card`);
* the factorial beats every exponential (`log_factorial_growth`, from Stirling);
* hence `k ≤ c log n` for large `n` (`omega_le_mul_log`), and exponentiating gives the claim.
-/

namespace Work.BMF

open Finset Nat

/-- **Counting bound.**  A finset of naturals, all at least `2` and all at most `M`, has at most
`M - 1` elements.  Proof: `b ↦ b - 2` is injective on `s` and maps it into `Finset.range (M-1)`. -/
lemma card_add_one_le_of_le (s : Finset ℕ) {M : ℕ} (hM2 : 2 ≤ M) (h2 : ∀ a ∈ s, 2 ≤ a)
    (hM : ∀ a ∈ s, a ≤ M) : s.card + 1 ≤ M := by
  have hinj : Set.InjOn (fun b : ℕ => b - 2) ↑s := by
    intro x hx y hy hxy
    beta_reduce at hxy
    have hx2 : 2 ≤ x := h2 x hx
    have hy2 : 2 ≤ y := h2 y hy
    omega
  have himg : (s.image (fun b => b - 2)).card = s.card := Finset.card_image_of_injOn hinj
  have hsub : s.image (fun b => b - 2) ⊆ Finset.range (M - 1) := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨b, hb, rfl⟩
    rw [Finset.mem_range]
    have hbM : b ≤ M := hM b hb
    have hb2 : 2 ≤ b := h2 b hb
    omega
  have hle := Finset.card_le_card hsub
  rw [himg, Finset.card_range] at hle
  omega

/-- `∏_{i<k} (2 + i) = (k+1)!`. -/
lemma prod_range_add_two (k : ℕ) : ∏ i ∈ Finset.range k, (2 + i) = (k + 1).factorial := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ (n+1)]; ring

/-- **The product of `k` distinct integers `≥ 2` is at least `(k+1)!`.**  More precisely, for a
finset `s` of naturals all `≥ 2`, `∏_{i < s.card} (2 + i) ≤ ∏_{a ∈ s} a`.  The bound is sharp,
`s = {2, …, k+1}` giving equality.

Induction on the maximum (`Finset.induction_on_max`): removing the maximum `a` leaves `s` with
`s.card + 1 = (insert a s).card` elements, all `≤ a` and `≥ 2`, so `s.card + 2 ≤ a`
(`card_add_one_le_of_le`); the induction hypothesis bounds `∏_{x ∈ s} x` from below by
`∏_{i < s.card} (2+i) = (s.card+1)!` (`prod_range_add_two`), and
`(s.card+1)! · (s.card+2) = (s.card+2)! = ∏_{i < s.card+1} (2+i)`. -/
lemma prod_range_two_le_prod (s : Finset ℕ) (h : ∀ a ∈ s, 2 ≤ a) :
    ∏ i ∈ Finset.range s.card, (2 + i) ≤ ∏ a ∈ s, a := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha_not : a ∉ s := fun hc => absurd (hlt a hc) (lt_irrefl a)
    rw [Finset.card_insert_of_notMem ha_not, Finset.prod_insert ha_not, Finset.prod_range_succ]
    have hs2 : ∀ x ∈ s, 2 ≤ x := fun x hx => h x (Finset.mem_insert_of_mem hx)
    have ha2 : 2 ≤ a := h a (Finset.mem_insert_self a s)
    have hcard_raw : (insert a s).card + 1 ≤ a :=
      card_add_one_le_of_le (insert a s) ha2 h (fun x hx => by
        rcases Finset.mem_insert.mp hx with hxa | hxs
        · exact le_of_eq hxa
        · exact le_of_lt (hlt x hxs))
    have hcard : 2 + s.card ≤ a := by
      rw [Finset.card_insert_of_notMem ha_not] at hcard_raw
      omega
    calc (∏ i ∈ Finset.range s.card, (2 + i)) * (2 + s.card)
        ≤ (∏ x ∈ s, x) * (2 + s.card) := Nat.mul_le_mul_right _ (ih hs2)
      _ ≤ (∏ x ∈ s, x) * a := Nat.mul_le_mul_left _ hcard
      _ = a * ∏ x ∈ s, x := by ring

/-- **A product of distinct naturals each `≥ 2` dominates a factorial.**  If every element of
`s : Finset ℕ` is at least `2`, then `(s.card + 1)! ≤ ∏ a ∈ s, a`.  This is the combinatorial
input for `ω(n) = o(log n)`. -/
lemma prod_ge_factorial_card (s : Finset ℕ) (h : ∀ a ∈ s, 2 ≤ a) :
    (s.card + 1).factorial ≤ ∏ a ∈ s, a := by
  have h1 := prod_range_two_le_prod s h
  rwa [prod_range_add_two] at h1

/-- **The factorial grows faster than any exponential.**  For every `C > 0` there is `K` such
that `k * C ≤ log ((k+1)!)` for all `k ≥ K`.

Immediate from Stirling's lower bound for `log n!` (`Stirling.le_log_factorial_stirling`): with
`n = k+1`, `log ((k+1)!) ≥ (k+1) log(k+1) - (k+1) + log(k+1)/2 + log(2π)/2 → ∞` faster than
`C k`. -/
lemma log_factorial_growth (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (k : ℝ) * C ≤ Real.log ((k + 1).factorial) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (1 + 2 * C))
  refine ⟨K, fun k hk => ?_⟩
  have hkR : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : Real.exp (1 + 2 * C) < (k : ℝ) + 1 := by linarith
  have hlog : 1 + 2 * C < Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_exp (1 + 2 * C)]
    exact Real.log_lt_log (Real.exp_pos _) hexp
  have hst := Stirling.le_log_factorial_stirling (n := k + 1) (by omega)
  push_cast at hst
  have hpi : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hk0 : (0 : ℝ) ≤ k := by positivity
  nlinarith [hst, hlog, hpi, hk0, hC]

/-- **`ω(n) = o(log n)`.**  For every `c > 0` there is `N` such that
`ω(n) = n.primeFactors.card ≤ c · log n` for all `n ≥ N`.

Route: `∏_{p ∣ n} p ∣ n` so `(ω(n)+1)! ≤ ∏_{p ∣ n} p ≤ n` (`prod_ge_factorial_card` and
`Nat.prod_primeFactors_dvd`), and `(k+1)!` dominates `exp(k/c)` for large `k`
(`log_factorial_growth`). -/
lemma omega_le_mul_log (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n.primeFactors.card : ℝ) ≤ c * Real.log n := by
  obtain ⟨K, hK⟩ := log_factorial_growth (1 / c) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp ((K : ℝ) / c))
  refine ⟨max (max K 2) N₀, fun n hn => ?_⟩
  have hNK : K ≤ max (max K 2) N₀ := le_trans (le_max_left K 2) (le_max_left (max K 2) N₀)
  have hN2 : 2 ≤ max (max K 2) N₀ := le_trans (le_max_right K 2) (le_max_left (max K 2) N₀)
  have hNN₀ : N₀ ≤ max (max K 2) N₀ := le_max_right (max K 2) N₀
  have hnK : K ≤ n := le_trans hNK hn
  have hn2 : 2 ≤ n := le_trans hN2 hn
  have hnN₀ : N₀ ≤ n := le_trans hNN₀ hn
  set k := n.primeFactors.card with hk
  by_cases h : K ≤ k
  · -- `k ≥ K`: the factorial bound applies directly.
    have h1 := hK k h
    have h1' : (k : ℝ) ≤ c * Real.log ((k + 1).factorial) := by
      have hm := mul_le_mul_of_nonneg_right h1 (le_of_lt hc)
      have hsimp : ((k : ℝ) * (1 / c)) * c = (k : ℝ) := by field_simp
      rwa [hsimp, mul_comm] at hm
    have hfac : ((k + 1).factorial : ℕ) ≤ ∏ p ∈ n.primeFactors, p := by
      have hpro := prod_ge_factorial_card n.primeFactors
        (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
      rwa [← hk] at hpro
    have hP : ∏ p ∈ n.primeFactors, p ≤ n :=
      Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
    have hfacn : ((k + 1).factorial : ℕ) ≤ n := le_trans hfac hP
    have hlogfac : Real.log ((k + 1).factorial) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by exact_mod_cast hfacn)
    exact le_trans h1' (mul_le_mul_of_nonneg_left hlogfac (le_of_lt hc))
  · -- `k < K`: then `ω(n)` is bounded by the constant `K-1`, and `n ≥ N₀` is enormous.
    have hkK : k < K := not_le.mp h
    have hkR : (k : ℝ) < (K : ℝ) := by exact_mod_cast hkK
    have hexpK : Real.exp ((k : ℝ) / c) ≤ Real.exp ((K : ℝ) / c) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (le_of_lt hkR) (le_of_lt hc))
    have hexpn : Real.exp ((k : ℝ) / c) < (n : ℝ) :=
      lt_of_le_of_lt hexpK (lt_of_lt_of_le hN₀ (by exact_mod_cast hnN₀))
    have hlogn : (k : ℝ) / c < Real.log n := by
      have hlt := Real.log_lt_log (Real.exp_pos _) hexpn
      rwa [Real.log_exp] at hlt
    have hfin : (k : ℝ) < c * Real.log n := by
      have hm := mul_lt_mul_of_pos_right hlogn hc
      rwa [div_mul_cancel₀ _ (ne_of_gt hc), mul_comm] at hm
    exact le_of_lt hfin

/-- **`(2m)^{ω(q)}` is sub-polynomial in `q`.**  For every `ℓ ≥ 1`, `m ≥ 1` there is `q₀` with
`(2m)^{ω(q)} ≤ q^{1/(2ℓ)}` for all `q ≥ q₀`. -/
lemma n4_omega_rpow_bound (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) ^ ((1 : ℝ) / (2 * (ℓ : ℝ))) := by
  have hlogA : 0 < Real.log (((2 * m : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * m))
  have hApos : (0:ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have hlr : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  -- Apply `ω(n) = o(log n)` with `c = 1 / (2ℓ log(2m))`.
  have hc : 0 < 1 / (2 * (ℓ : ℝ) * Real.log (((2 * m : ℕ) : ℝ))) :=
    one_div_pos.mpr (mul_pos (by linarith) hlogA)
  obtain ⟨N, hN⟩ := omega_le_mul_log (1 / (2 * (ℓ : ℝ) * Real.log (((2 * m : ℕ) : ℝ)))) hc
  refine ⟨max N 2, fun q hq => ?_⟩
  have hqN : N ≤ q := le_trans (le_max_left N 2) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right N 2) hq
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hk := hN q hqN
  -- Turn `ω(q) ≤ log q / (2ℓ log 2m)` into `ω(q) log(2m) ≤ log q / (2ℓ)`.
  have h2 : (q.primeFactors.card : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) ≤
      (1 / (2 * (ℓ : ℝ))) * Real.log q := by
    have hmul := mul_le_mul_of_nonneg_right hk (le_of_lt hlogA)
    have heq : (1 / (2 * (ℓ : ℝ) * Real.log (((2 * m : ℕ) : ℝ)))) * Real.log q
        * Real.log (((2 * m : ℕ) : ℝ)) = (1 / (2 * (ℓ : ℝ))) * Real.log q := by
      field_simp
    rwa [heq] at hmul
  -- Exponentiate.
  apply (Real.log_le_log_iff (pow_pos hApos _) (Real.rpow_pos_of_pos hqpos _)).mp
  rw [Real.log_pow, Real.log_rpow hqpos]
  exact h2

end Work.BMF
