import Mathlib
import Submission.Theorem35Main
import Submission.LevelOfDistribution
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform
import Submission.Commons.NumberTheory.ArithmeticFunction.card_tuples_prod_lcm_eq_le
import Submission.Commons.NumberTheory.ArithmeticFunction.card_fibre_prod_lcm_le
import Submission.Commons.NumberTheory.CongruenceWindows.exists_mem_Icc_mod_shift

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 4000000

/-!
# Polymath8a Theorem 3.5(i): the discrepancy half (P8 (46))

This module proves the discrepancy estimate of Polymath8a Theorem 3.5(i): for
the `θ`-weighted window product of `Submission.S2Reduction`, the part
`thetaDiscSum` coming from the discrepancies `Δ(θ·1_{[x+h,2x+h]}; a (q))` is
`o(main term)`, using the level-of-distribution input
`Submission.LevelOfDistribution.levelOfDistribution ϑ`.

The structure follows P8 §4.2 verbatim:

* an elementary *crude bound* on a single discrepancy,
  `|Δ(θ·1_{[x+h,2x+h]}; c (q))| ≤ 4·τ(q)·(x/q + 2)·log (2x+h+1)`
  (`abs_discShift_theta_le`);
* a fibre count: at most `τ(M)^{3k}` good divisor tuples give `∏ᵢ[dᵢ,eᵢ] = M`
  (`card_goodFiberLe`);
* Cauchy--Schwarz against `levelOfDistribution ϑ` and the divisor-sum bound
  `Σ_{M ≤ Q} τ(M)^{B}/φ(M) ≪ (log Q)^{2^B}` (commons).
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-! ## Elementary bounds for `thetaNat` -/

lemma thetaNat_le_log_gen (n : ℕ) : thetaNat n ≤ Real.log (n : ℝ) := by
  rw [thetaNat]
  split_ifs with h
  · exact le_refl _
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · exact Real.log_nonneg (by exact_mod_cast h0)

/-- The number of `m ∈ [a, a+L]` in a single residue class modulo `q ≥ 1` is at
most `L/q + 2`. -/
lemma card_filter_mod_le (a L q c : ℕ) (hq : 1 ≤ q) :
    ((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).card ≤ L / q + 2 := by
  classical
  have hinj : Set.InjOn (fun m => m / q)
      ↑((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)) := by
    intro m hm m' hm' h
    have h1 : m % q = c % q := (Finset.mem_filter.mp hm).2
    have h2 : m' % q = c % q := (Finset.mem_filter.mp hm').2
    have h' : m / q = m' / q := h
    calc m = q * (m / q) + m % q := (Nat.div_add_mod m q).symm
      _ = q * (m' / q) + m' % q := by rw [h', h1, h2]
      _ = m' := Nat.div_add_mod m' q
  have hcard : ((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).card =
      (((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).image
        (fun m => m / q)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).image
        (fun m => m / q)) ⊆ Finset.Icc (a / q) ((a + L) / q) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hm.1.1, Nat.div_le_div_right hm.1.2⟩
  have key : (a + L) / q ≤ a / q + L / q + 1 := by
    have ha := Nat.div_add_mod a q
    have hmod : a % q < q := Nat.mod_lt _ (by omega)
    have h1 : (a + L) / q = a / q + (a % q + L) / q := by
      conv_lhs => rw [← ha]
      rw [show q * (a / q) + a % q + L = q * (a / q) + (a % q + L) by ring]
      rw [Nat.mul_add_div (by omega : 0 < q)]
    have h2 : (a % q + L) / q ≤ L / q + 1 := by
      have h3 : a % q + L ≤ (L - 1) + q * 1 := by omega
      have h4 : ((L - 1) + q * 1) / q = (L - 1) / q + 1 := Nat.add_mul_div_left _ _ (by omega)
      calc (a % q + L) / q ≤ ((L - 1) + q * 1) / q := Nat.div_le_div_right h3
        _ = (L - 1) / q + 1 := h4
        _ ≤ L / q + 1 := by
            have : (L - 1) / q ≤ L / q := Nat.div_le_div_right (by omega)
            omega
    omega
  have hle : a / q ≤ (a + L) / q := Nat.div_le_div_right (by omega)
  calc ((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).card
      = (((Finset.Icc a (a + L)).filter (fun m => m % q = c % q)).image
          (fun m => m / q)).card := hcard
    _ ≤ (Finset.Icc (a / q) ((a + L) / q)).card := Finset.card_le_card hsub
    _ = (a + L) / q + 1 - a / q := Nat.card_Icc _ _
    _ = ((a + L) / q - a / q) + 1 := by omega
    _ ≤ L / q + 1 + 1 := by omega
    _ = L / q + 2 := by omega

/-! ## The divisor bound `1/φ(q) ≤ τ(q)/q` -/

/-- `q ≤ φ(q)·τ(q)`: the number of divisors of `q` dominates the ratio
`q/φ(q) = ∏_{p | q} p/(p-1) ≤ ∏_{p | q} 2`. -/
theorem totient_mul_card_divisors_ge (q : ℕ) : q ≤ q.totient * q.divisors.card := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  have hcard : q.divisors.card = ∏ p ∈ q.primeFactors, (q.factorization p + 1) :=
    Nat.card_divisors (by omega)
  have htot : q.totient = ∏ p ∈ q.primeFactors, (p ^ (q.factorization p - 1) * (p - 1)) := by
    rw [Nat.totient_eq_prod_factorization (by omega),
      Nat.prod_factorization_eq_prod_primeFactors]
  have hqprod : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p :=
    Nat.prod_primeFactors_pow_factorization (by omega)
  rw [hcard, htot]
  conv_lhs => rw [hqprod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    have he1 : 1 ≤ q.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpp (by omega)).mp hdvd
    have h2 : 2 ≤ p := hpp.two_le
    have h3 : p ^ q.factorization p = p ^ (q.factorization p - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel he1]
    have h4 : p ≤ (p - 1) * (q.factorization p + 1) := by
      have : (p - 1) * (q.factorization p + 1) = (p - 1) * q.factorization p + (p - 1) := by ring
      have h5 : p - 1 ≤ (p - 1) * q.factorization p := by
        calc p - 1 = (p - 1) * 1 := (mul_one _).symm
          _ ≤ (p - 1) * q.factorization p := Nat.mul_le_mul_left _ he1
      omega
    calc p ^ q.factorization p = p ^ (q.factorization p - 1) * p := h3
      _ ≤ p ^ (q.factorization p - 1) * ((p - 1) * (q.factorization p + 1)) := by
          exact Nat.mul_le_mul_left _ h4
      _ = p ^ (q.factorization p - 1) * (p - 1) * (q.factorization p + 1) := by ring

/-- The real form of the divisor ratio bound: `1/φ(q) ≤ τ(q)/q`. -/
theorem inv_totient_le_card_divisors_div (q : ℕ) :
    (1 : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / (q : ℝ) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  have htot : (0 : ℝ) < (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr hq
    exact_mod_cast this
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [div_le_iff₀ htot, div_mul_eq_mul_div, le_div_iff₀ hqR, one_mul]
  have h2 : ((q : ℝ)) ≤ ((q.totient : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast totient_mul_card_divisors_ge q
  linarith

/-! ## The crude bound on a single discrepancy

P8 §4.2 uses `|Δ(1_{[x+h,2x+h]}θ; a (q))| ≪ (x/q)·log^{O(1)}x`.  We record the
explicit, fully elementary version
`|Δ| ≤ 2·τ(q)·(x/q + 2)·log(2x+h+1)`. -/

/-- The upper end of the shifted window `[x+h, 2x+h]`, plus one. -/
def windowUp (x h : ℕ) : ℕ := 2 * x + h + 1

/-- `log (2x + h + 1) ≥ 0`. -/
lemma log_window_nonneg (x h : ℕ) : (0 : ℝ) ≤ Real.log ((windowUp x h : ℕ) : ℝ) := by
  apply Real.log_nonneg
  show (1 : ℝ) ≤ ((2 * x + h + 1 : ℕ) : ℝ)
  exact_mod_cast (by omega : 1 ≤ 2 * x + h + 1)

/-- A single `thetaNat` is bounded by `log B` as soon as its argument is `≤ B`. -/
lemma thetaNat_le_log_of_le {m B : ℕ} (hm : m ≤ B) (hB : 1 ≤ B) :
    thetaNat m ≤ Real.log ((B : ℕ) : ℝ) := by
  by_cases h : m.Prime
  · rw [thetaNat, if_pos h]
    exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hm)
  · rw [thetaNat, if_neg h]
    exact Real.log_nonneg (by exact_mod_cast hB)

/-- A window sum of `thetaNat` is bounded by `#s · log B`. -/
lemma sum_thetaNat_le_card (s : Finset ℕ) (h B : ℕ)
    (hB : ∀ n ∈ s, n + h ≤ B) (hB1 : 1 ≤ B) :
    ∑ n ∈ s, thetaNat (n + h) ≤ (s.card : ℝ) * Real.log ((B : ℕ) : ℝ) := by
  calc ∑ n ∈ s, thetaNat (n + h) ≤ ∑ _n ∈ s, Real.log ((B : ℕ) : ℝ) :=
        Finset.sum_le_sum fun n hn => thetaNat_le_log_of_le (hB n hn) hB1
    _ = (s.card : ℝ) * Real.log ((B : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The number of `m ∈ [a, a+L]` with `(m + h)` in a fixed class modulo `q ≥ 1`
is at most `L/q + 2`. -/
lemma card_filter_mod_shift_le (a L q c h : ℕ) (hq : 1 ≤ q) :
    ((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).card ≤ L / q + 2 := by
  classical
  have hinj : Set.InjOn (fun m => (m + h) / q)
      ↑((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)) := by
    intro m hm m' hm' h'
    have h1 : (m + h) % q = c % q := (Finset.mem_filter.mp hm).2
    have h2 : (m' + h) % q = c % q := (Finset.mem_filter.mp hm').2
    have h'' : (m + h) / q = (m' + h) / q := h'
    have : m + h = m' + h := by
      calc m + h = q * ((m + h) / q) + (m + h) % q := (Nat.div_add_mod (m + h) q).symm
        _ = q * ((m' + h) / q) + (m' + h) % q := by rw [h'', h1, h2]
        _ = m' + h := Nat.div_add_mod (m' + h) q
    omega
  have hcard : ((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).card =
      (((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).image
        (fun m => (m + h) / q)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : (((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).image
        (fun m => (m + h) / q)) ⊆ Finset.Icc ((a + h) / q) ((a + L + h) / q) := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    refine Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (by omega),
      Nat.div_le_div_right (by omega)⟩
  have key : (a + L + h) / q ≤ (a + h) / q + L / q + 1 := by
    have ha := Nat.div_add_mod (a + h) q
    have h1 : (a + h + L) / q = (a + h) / q + ((a + h) % q + L) / q := by
      conv_lhs => rw [← ha]
      rw [show q * ((a + h) / q) + (a + h) % q + L = q * ((a + h) / q) + ((a + h) % q + L)
        by ring]
      rw [Nat.mul_add_div (by omega : 0 < q)]
    have h2 : ((a + h) % q + L) / q ≤ L / q + 1 := by
      have hmod : (a + h) % q < q := Nat.mod_lt _ (by omega)
      have h3 : (a + h) % q + L ≤ (L - 1) + q * 1 := by omega
      have h4 : ((L - 1) + q * 1) / q = (L - 1) / q + 1 := Nat.add_mul_div_left _ _ (by omega)
      calc ((a + h) % q + L) / q ≤ ((L - 1) + q * 1) / q := Nat.div_le_div_right h3
        _ = (L - 1) / q + 1 := h4
        _ ≤ L / q + 1 := by
            have : (L - 1) / q ≤ L / q := Nat.div_le_div_right (by omega)
            omega
    have e1 : (a + h + L) / q = (a + L + h) / q := by congr 1; omega
    rw [e1] at h1
    omega
  have hle : (a + h) / q ≤ (a + L + h) / q := Nat.div_le_div_right (by omega)
  calc ((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).card
      = (((Finset.Icc a (a + L)).filter (fun m => (m + h) % q = c % q)).image
          (fun m => (m + h) / q)).card := hcard
    _ ≤ (Finset.Icc ((a + h) / q) ((a + L + h) / q)).card := Finset.card_le_card hsub
    _ = (a + L + h) / q + 1 - (a + h) / q := Nat.card_Icc _ _
    _ = ((a + L + h) / q - (a + h) / q) + 1 := by omega
    _ ≤ L / q + 1 + 1 := by omega
    _ = L / q + 2 := by omega

/-- The class filter inside `[x, 2x]` has at most `x/q + 2` elements. -/
lemma card_classFilter_le (x q c h : ℕ) (hq : 1 ≤ q) :
    ((Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q)).card ≤ x / q + 2 := by
  have hIcc : (Finset.Icc x (2 * x) : Finset ℕ) = Finset.Icc x (x + x) := by
    congr 1; omega
  rw [hIcc]
  exact card_filter_mod_shift_le x x q c h hq

/-- The `[x,2x]` window has `x + 1` elements. -/
lemma card_Icc_two_mul (x : ℕ) : (Finset.Icc x (2 * x)).card = x + 1 := by
  rw [Nat.card_Icc]
  omega

/-- The real card bound for the class filter. -/
lemma card_classFilter_le_real (x q c h : ℕ) (hq : 1 ≤ q) :
    (((Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q)).card : ℝ) ≤
      (x : ℝ) / q + 2 := by
  have hc := card_classFilter_le x q c h hq
  have h1 : (((x / q + 2 : ℕ)) : ℝ) = ((x / q : ℕ) : ℝ) + 2 := by push_cast; ring
  have h2 : (((Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q)).card : ℝ) ≤
      ((x / q + 2 : ℕ) : ℝ) := by exact_mod_cast hc
  have h3 : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / q := Nat.cast_div_le
  linarith

/-- The real card bound for the coprime-class filter. -/
lemma card_copFilter_le_real (x q h : ℕ) :
    (((Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q)).card : ℝ) ≤
      (x : ℝ) + 1 := by
  have h1 : ((Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q)).card ≤ x + 1 := by
    calc _ ≤ (Finset.Icc x (2 * x)).card := Finset.card_filter_le _ _
      _ = x + 1 := card_Icc_two_mul x
  exact_mod_cast h1

/-- **Class part of the crude bound.** -/
lemma discShift_class_sum_le (x q c h : ℕ) (hq : 1 ≤ q) (hx : 1 ≤ x) :
    (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q), thetaNat (n + h)) ≤
      ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
  have hcard := card_classFilter_le_real x q c h hq
  have hlog0 : (0 : ℝ) ≤ Real.log ((windowUp x h : ℕ) : ℝ) := log_window_nonneg x h
  calc (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q), thetaNat (n + h))
      ≤ (((Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q)).card : ℝ) *
          Real.log ((windowUp x h : ℕ) : ℝ) := by
        refine sum_thetaNat_le_card _ h _ ?_ (by show 1 ≤ 2 * x + h + 1; omega)
        intro n hn
        have h2 := (Finset.mem_filter.mp hn).1
        have h3 := (Finset.mem_Icc.mp h2).2
        show n + h ≤ 2 * x + h + 1
        omega
    _ ≤ ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcard hlog0

/-- **Coprime-class part of the crude bound.** -/
lemma discShift_cop_sum_le (x q h : ℕ) (hx : 1 ≤ x) :
    (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h)) ≤
      ((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ) := by
  have hcard := card_copFilter_le_real x q h
  have hlog0 : (0 : ℝ) ≤ Real.log ((windowUp x h : ℕ) : ℝ) := log_window_nonneg x h
  calc (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h))
      ≤ (((Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q)).card : ℝ) *
          Real.log ((windowUp x h : ℕ) : ℝ) := by
        refine sum_thetaNat_le_card _ h _ ?_ (by show 1 ≤ 2 * x + h + 1; omega)
        intro n hn
        have h2 := (Finset.mem_filter.mp hn).1
        have h3 := (Finset.mem_Icc.mp h2).2
        show n + h ≤ 2 * x + h + 1
        omega
    _ ≤ ((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcard hlog0

/-- `(x+1)/q ≤ 2(x/q + 2)`. -/
lemma add_one_div_le_two (x q : ℕ) (hq : 1 ≤ q) :
    ((x : ℝ) + 1) / q ≤ 2 * ((x : ℝ) / q + 2) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [add_div]
  have h1 : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one hqR]; exact_mod_cast hq
  have h2 : (0 : ℝ) ≤ (x : ℝ) / q := by positivity
  linarith

/-- **The crude discrepancy bound (P8 §4.2).**  For `q ≥ 1` and `x ≥ 1`,
`|Δ(1_{[x+h,2x+h]}θ; c (q))| ≤ 2·τ(q)·(x/q + 2)·log(2x+h+1)`. -/
theorem abs_discShift_theta_le (x q c h : ℕ) (hq : 1 ≤ q) (hx : 1 ≤ x) :
    |discShift (fun n => thetaNat n) x q c h| ≤
      2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hτ1 : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
    have : 1 ≤ q.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) ≤ (q.divisors.card : ℝ) := by positivity
  have hlog0 : (0 : ℝ) ≤ Real.log ((windowUp x h : ℕ) : ℝ) := log_window_nonneg x h
  have hφinv : (1 : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / (q : ℝ) :=
    inv_totient_le_card_divisors_div q
  have hφ0 : (0 : ℝ) < (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hA := discShift_class_sum_le x q c h hq hx
  have hB := discShift_cop_sum_le x q h hx
  have hA0 : (0 : ℝ) ≤ ∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q),
      thetaNat (n + h) := Finset.sum_nonneg fun n _ => thetaNat_nonneg _
  have hB0 : (0 : ℝ) ≤ ∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q),
      thetaNat (n + h) := Finset.sum_nonneg fun n _ => thetaNat_nonneg _
  have hK0 : (0 : ℝ) ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) *
      Real.log ((windowUp x h : ℕ) : ℝ) := by positivity
  have h1 : (1 / (q.totient : ℝ)) *
        (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h))
      ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
    have hstep1 : (1 / (q.totient : ℝ)) *
          (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h))
        ≤ ((q.divisors.card : ℝ) / (q : ℝ)) *
          (((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ)) := by
      have h20 : (1 / (q.totient : ℝ)) *
            (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h))
          ≤ (1 / (q.totient : ℝ)) * (((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      exact le_trans h20 (mul_le_mul_of_nonneg_right hφinv (by positivity))
    have hstep2 : ((q.divisors.card : ℝ) / (q : ℝ)) *
          (((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ))
        ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
      have h4 := add_one_div_le_two x q hq
      have h5 : ((x : ℝ) + 1) / q * Real.log ((windowUp x h : ℕ) : ℝ) ≤
          (2 * ((x : ℝ) / q + 2)) * Real.log ((windowUp x h : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hlog0
      have hrw : ((q.divisors.card : ℝ) / (q : ℝ)) *
            (((x : ℝ) + 1) * Real.log ((windowUp x h : ℕ) : ℝ))
          = (q.divisors.card : ℝ) * (((x : ℝ) + 1) / q * Real.log ((windowUp x h : ℕ) : ℝ)) := by
        ring
      have hrw2 : (q.divisors.card : ℝ) *
            ((2 * ((x : ℝ) / q + 2)) * Real.log ((windowUp x h : ℕ) : ℝ))
          = 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) *
            Real.log ((windowUp x h : ℕ) : ℝ) := by ring
      rw [hrw, ← hrw2]
      exact mul_le_mul_of_nonneg_left h5 hτ0
    exact le_trans hstep1 hstep2
  have h2 : (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q),
        thetaNat (n + h))
      ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
    refine le_trans hA ?_
    have h6 : (1 : ℝ) ≤ 2 * (q.divisors.card : ℝ) := by linarith
    have h7 : (0 : ℝ) ≤ ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ (x : ℝ) / q + 2 := by positivity
      positivity
    have h8 := le_mul_of_one_le_left h7 h6
    have hrw3 : (2 * (q.divisors.card : ℝ)) *
          (((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ))
        = 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) *
          Real.log ((windowUp x h : ℕ) : ℝ) := by ring
    linarith [h8, hrw3.le, hrw3.ge]
  rw [discShift, abs_le]
  refine ⟨?_, ?_⟩
  · have h9 : (1 / (q.totient : ℝ)) *
          (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h)) -
          (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q), thetaNat (n + h))
        ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) *
          Real.log ((windowUp x h : ℕ) : ℝ) := by
      linarith [h1, sub_le_self ((1 / (q.totient : ℝ)) *
        (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q),
          thetaNat (n + h))) hA0]
    linarith [h9]
  · have h10 : (0 : ℝ) ≤ (1 / (q.totient : ℝ)) *
        (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), thetaNat (n + h)) :=
      mul_nonneg (by positivity) hB0
    linarith [h2, h10]

/-! ## Primitivity of the CRT class

P8 §4.2: "we may use the Chinese remainder theorem to concatenate the
congruence conditions on `n` into a single **primitive** congruence condition
`n + h_k ≡ a (mod q)`".  This is the compatibility of the level-of-distribution
input (`sup` over *primitive* classes) with the class produced by `classResidue`:
for a good divisor pair the CRT class is coprime to `q = W·∏ᵢ[dᵢ,eᵢ]`.

The proof: pick `n ∈ Sset`; then `(n+h) ≡ c (mod q)`, so `gcd c q = gcd (n+h) q`.
Now `(n+h) ⊥ W` (because `n ≡ b (W)` and `b + h ⊥ W`), and `(n+h) ⊥ m i` (because
`m i | n + H i`, so `n + h ≡ h - H i (mod m i)`, and `|h - H i| < wd` while every
prime factor of `m i` exceeds `wd`). -/

/-- Every prime factor of a modulus coprime to `W` exceeds `wd`, when every prime
`≤ wd` divides `W`. -/
lemma prime_gt_wd_of_dvd_of_coprime_W {m W wd p : ℕ}
    (hWdiv : ∀ p : ℕ, Nat.Prime p → p ≤ wd → p ∣ W)
    (hcop : m.Coprime W) (hp : Nat.Prime p) (hpm : p ∣ m) : wd < p := by
  by_contra hcon
  push_neg at hcon
  have hpW : p ∣ W := hWdiv p hp hcon
  have : p ∣ m.gcd W := Nat.dvd_gcd hpm hpW
  rw [hcop.gcd_eq_one] at this
  exact hp.not_dvd_one this

/-- `n + h` is coprime to `m` when `m | n + H`, `m ⊥ W`, all primes `≤ wd` divide
`W`, and the shift `h` differs from `H` by less than `wd`. -/
lemma coprime_add_of_dvd_add {n h H m wd W : ℕ}
    (hWdiv : ∀ p : ℕ, Nat.Prime p → p ≤ wd → p ∣ W)
    (hcop : m.Coprime W) (hdvd : m ∣ n + H) (hhne : h ≠ H)
    (h1 : h - H < wd) (h2 : H - h < wd) :
    (n + h).Coprime m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set g : ℕ := Nat.gcd (n + h) m with hgdef
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hgn : g ∣ n + h := Nat.gcd_dvd_left _ _
  have hgH : g ∣ n + H := Nat.dvd_trans hgm hdvd
  have hgne : g ≠ 0 := by
    intro hzero
    have hz : Nat.gcd (n + h) m = 0 := by rw [← hgdef]; exact hzero
    obtain ⟨hz1, hz2⟩ := Nat.gcd_eq_zero_iff.mp hz
    have hzero2 : n + H = 0 := by
      rw [hz2] at hdvd
      exact Nat.eq_zero_of_zero_dvd hdvd
    have hn0 : n = 0 := by omega
    have hh0 : h = 0 := by omega
    have hH0 : H = 0 := by omega
    exact hhne (by omega)
  have hgwd : g < wd := by
    rcases le_total h H with hh | hh
    · have hpos : 0 < H - h := by omega
      have hdvd' : g ∣ H - h := by
        have hsub : g ∣ (n + H) - (n + h) := Nat.dvd_sub hgH hgn
        rwa [show n + H - (n + h) = H - h by omega] at hsub
      have hle : g ≤ H - h := Nat.le_of_dvd hpos hdvd'
      omega
    · have hpos : 0 < h - H := by omega
      have hdvd' : g ∣ h - H := by
        have hsub : g ∣ (n + h) - (n + H) := Nat.dvd_sub hgn hgH
        rwa [show n + h - (n + H) = h - H by omega] at hsub
      have hle : g ≤ h - H := Nat.le_of_dvd hpos hdvd'
      omega
  by_contra hgne1
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgne1
  have hpm : p ∣ m := Nat.dvd_trans hpg hgm
  have hple : p ≤ g := Nat.le_of_dvd (by omega) hpg
  exact absurd (prime_gt_wd_of_dvd_of_coprime_W hWdiv hcop hp hpm) (by omega)

/-- `a.Coprime q ↔ b.Coprime q` when `a` and `b` are congruent modulo `q`. -/
lemma coprime_iff_of_mod_eq {a b q : ℕ} (h : a % q = b % q) :
    a.Coprime q ↔ b.Coprime q := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  have h1 : a.gcd q = (a % q).gcd q := by rw [Nat.gcd_comm, Nat.gcd_rec q a, Nat.gcd_comm]
  have h2 : b.gcd q = (b % q).gcd q := by rw [Nat.gcd_comm, Nat.gcd_rec q b, Nat.gcd_comm]
  rw [h1, h2, h]

/-- There is a member of `[N,2N]` in the residue class `c - h (mod q)` when
`q ≤ N`. -/
lemma exists_mem_Icc_mod_shift_local (N q c h : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N) :
    ∃ n ∈ Finset.Icc N (2 * N), (n + h) % q = c % q := by
  set r : ℕ := (c + q - h % q) % q with hrdef
  have hqpos : 0 < q := by omega
  have hrq : r < q := Nat.mod_lt _ hqpos
  have hmodr : (r + h) % q = c % q := by
    have h0 : r ≡ c + q - h % q [MOD q] := by rw [hrdef]; exact Nat.mod_modEq _ _
    have h1 : h ≡ h % q [MOD q] := (Nat.mod_modEq h q).symm
    have h2 : r + h ≡ (c + q - h % q) + h % q [MOD q] := h0.add h1
    have hqle : h % q ≤ c + q :=
      le_trans (Nat.le_of_lt (Nat.mod_lt h hqpos)) (Nat.le_add_left q c)
    have h3 : (c + q - h % q) + h % q = c + q := Nat.sub_add_cancel hqle
    have h5 : c + q ≡ c [MOD q] := by
      rw [Nat.ModEq]
      simpa using Nat.add_mul_mod_self_left c q 1
    have h4 : (r + h) ≡ c [MOD q] := by
      rw [h3] at h2
      exact h2.trans h5
    exact h4
  set k : ℕ := (N - r + q - 1) / q with hkdef
  have hk1 : N - r ≤ q * k := by
    have h := Nat.div_add_mod (N - r + q - 1) q
    have hlt := Nat.mod_lt (N - r + q - 1) hqpos
    rw [hkdef]; omega
  have hk2 : q * k ≤ N - r + q - 1 := by
    have h := Nat.div_add_mod (N - r + q - 1) q
    rw [hkdef]; omega
  have hrN : r ≤ N := by omega
  refine ⟨r + q * k, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    constructor <;> omega
  · have hnmod : (r + q * k) % q = r := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrq]
    have hme : (r + q * k) ≡ r [MOD q] := by
      rw [Nat.ModEq]
      exact hnmod.trans (Nat.mod_eq_of_lt hrq).symm
    have hfin : (r + q * k) + h ≡ c [MOD q] := by
      have h' := hme.add_right h
      rw [Nat.ModEq] at h'
      rw [hmodr] at h'
      exact h'
    exact hfin

/-- **The CRT class of a good divisor pair is primitive.**  For a good pair (all
`[dᵢ,eᵢ]` coprime to `W` and pairwise coprime) and shifts with `h ≠ H i`,
`|h - H i| < wd x` and every prime `≤ wd x` dividing `W`, the class
`classResidue` is coprime to `q = W·∏ᵢ[dᵢ,eᵢ]`. -/
theorem classResidue_coprime {k N W b h wd : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ}
    (hW : 0 < W) (hm : ∀ i, 0 < m i)
    (hcop : ∀ i, (m i).Coprime W) (hcopm : ∀ i j, i ≠ j → (m i).Coprime (m j))
    (hWdiv : ∀ p : ℕ, Nat.Prime p → p ≤ wd → p ∣ W)
    (hbWh : (b + h).Coprime W)
    (hhne : ∀ i, h ≠ H i)
    (hseph : ∀ i, h - H i < wd ∧ H i - h < wd)
    (hqN : W * ∏ i, m i ≤ N) :
    (classResidue N W b h H m).Coprime (W * ∏ i, m i) := by
  classical
  have hqpos : 1 ≤ W * ∏ i, m i := by
    have h2 : 0 < ∏ i : Fin k, m i := Finset.prod_pos (fun i _ => hm i)
    exact Nat.succ_le_of_lt (Nat.mul_pos hW h2)
  have hspec := classResidue_spec N W b h H m (ne_of_gt hW)
    (fun i => ne_of_gt (hm i)) hcop hcopm
  obtain ⟨n, hnIcc, hnmod⟩ :=
    exists_mem_Icc_mod_shift_local N (W * ∏ i, m i) (classResidue N W b h H m) h hqpos hqN
  have hnS : n ∈ Sset N W b H m := by
    rw [hspec]
    exact Finset.mem_filter.mpr ⟨hnIcc, hnmod⟩
  have hnW : n % W = b % W := (Finset.mem_filter.mp hnS).2.1
  have hnHi : ∀ i : Fin k, m i ∣ n + H i := (Finset.mem_filter.mp hnS).2.2
  have hnhW : (n + h).Coprime W := window_add_coprime_W (W := W) hnW hbWh
  have hnhmi : ∀ i : Fin k, (n + h).Coprime (m i) := fun i =>
    coprime_add_of_dvd_add hWdiv (hcop i) (hnHi i) (hhne i) (hseph i).1 (hseph i).2
  have hnhq : (n + h).Coprime (W * ∏ i, m i) :=
    hnhW.mul_right (Nat.Coprime.prod_right (fun i _ => hnhmi i))
  exact (coprime_iff_of_mod_eq hnmod.symm).mpr hnhq


/-! ## The level-of-distribution sum and the pointwise bound

The single remaining ingredient is the integral-sum comparison.  We record

* `discSupShift_le_crude` and `abs_discShift_le_discSupShift`: the `sSup`
  behaves as expected;
* `lod_sum_le`: the level-of-distribution sum bounds `Σ_{q ≤ Q} discSupShift x q h`;
* `thetaDiscSum_pointwise_le`: the pointwise bound for the summands of
  `thetaDiscSum`, via the primitive CRT class. -/

/-- `log (2x+h+1)` is monotone in `h`. -/
lemma log_windowUp_mono {x h h' : ℕ} (hh : h ≤ h') :
    Real.log ((windowUp x h : ℕ) : ℝ) ≤ Real.log ((windowUp x h' : ℕ) : ℝ) := by
  apply Real.log_le_log
  · show (0 : ℝ) < ((windowUp x h : ℕ) : ℝ)
    exact_mod_cast (by show 0 < 2 * x + h + 1; omega)
  · exact_mod_cast (by show 2 * x + h + 1 ≤ 2 * x + h' + 1; omega)

/-- The primitive-class discrepancy is bounded by the crude bound. -/
lemma discSupShift_le_crude (x q h : ℕ) (hq : 1 ≤ q) (hx : 1 ≤ x) :
    discSupShift x q h ≤ 2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) *
      Real.log ((windowUp x h : ℕ) : ℝ) := by
  rw [discSupShift]
  refine csSup_le ⟨_, ⟨1, Nat.coprime_one_left q, rfl⟩⟩ ?_
  rintro y ⟨a, _, rfl⟩
  exact abs_discShift_theta_le x q a h hq hx

/-- A primitive class gives the `sSup` bound. -/
lemma abs_discShift_le_discSupShift (x q c h : ℕ) (hq : 1 ≤ q) (hx : 1 ≤ x)
    (hc : c.Coprime q) :
    |discShift (fun n => thetaNat n) x q c h| ≤ discSupShift x q h := by
  have hbdd : BddAbove ((fun a => |discShift (fun n => thetaNat n) x q a h|) ''
      {a : ℕ | a.Coprime q}) :=
    ⟨2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ),
      fun y hy => by rcases hy with ⟨a, _, rfl⟩; exact abs_discShift_theta_le x q a h hq hx⟩
  rw [discSupShift]
  exact le_csSup hbdd ⟨c, hc, rfl⟩

/-- The auxiliary level-of-distribution sum `Σ_{q ≤ Q} sup'_{h' ≤ h} discSupShift x q h'`,
bounded by `x·log^{-A}x` for every fixed `A`. -/
lemma lod_sum_le {ϑ : ℝ} (hlev : levelOfDistribution ϑ) (A : ℝ) (hA : 1 ≤ A) (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ, (Q : ℝ) ≤ (x : ℝ) ^ ϑ →
      (∑ q ∈ Finset.Icc 1 Q,
        (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
          (fun h' => discSupShift x q h')) ≤
        (x : ℝ) * (Real.log (x : ℝ)) ^ (-A) :=
  hlev A hA h

/-- `discSupShift x q h` is dominated by the level-of-distribution sup. -/
lemma discSupShift_le_lodSup (x q h : ℕ) :
    discSupShift x q h ≤
      (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
        (fun h' => discSupShift x q h') :=
  Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))


/-! ## The estimate: `thetaDiscSum = o(main term)` (P8 (46)) -/

/-- `log Wf(x)/√(log x) → 0` gives `Wf x ≤ x^c` eventually, for every `c > 0`. -/
lemma eventually_le_rpow_of_log_ratio' {W : ℕ → ℕ} (hWnz : ∀ x, W x ≠ 0) {c : ℝ}
    (hc : 0 < c)
    (hlq : Tendsto (fun x : ℕ =>
      Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ x : ℕ in atTop, ((W x : ℕ) : ℝ) ≤ (x : ℝ) ^ c := by
  have h1 : ∀ᶠ x : ℕ in atTop,
      Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)) < c / 2 :=
    (tendsto_order.1 hlq).2 (c / 2) (by linarith)
  have h2 : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have h3 : ∀ᶠ x : ℕ in atTop, 1 < x := eventually_ge_atTop 2
  refine (h1.and (h2.and h3)).mono fun x hx => ?_
  obtain ⟨h1x, h2x, h3x⟩ := hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hs : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hlog : Real.log ((W x : ℕ) : ℝ) ≤ c * Real.log (x : ℝ) := by
    have hWlt : Real.log ((W x : ℕ) : ℝ) < (c / 2) * Real.sqrt (Real.log (x : ℝ)) := by
      rw [div_lt_iff₀ hs] at h1x
      linarith
    have hsle : Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    nlinarith [hWlt, hsle, hc]
  have hWpos : (0 : ℝ) < ((W x : ℕ) : ℝ) := by
    have := Nat.pos_of_ne_zero (hWnz x)
    exact_mod_cast this
  calc ((W x : ℕ) : ℝ) = Real.exp (Real.log ((W x : ℕ) : ℝ)) := (Real.exp_log hWpos).symm
    _ ≤ Real.exp (c * Real.log (x : ℝ)) := Real.exp_le_exp.mpr hlog
    _ = (x : ℝ) ^ c := by
        rw [Real.rpow_def_of_pos hxpos]; ring_nf


/-- `|λ_{F,x}(d)| ≤ B` when `|F| ≤ B`. -/
lemma abs_lamDivWeight_le {F : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    (x d : ℕ) : |lamDivWeight F x d| ≤ B := by
  rw [lamDivWeight, abs_mul]
  calc |moebiusReal d| * |F (Real.log (d : ℝ) / Real.log (x : ℝ))| ≤ 1 * B :=
        mul_le_mul (abs_moebiusReal_le_one d) (hF _) (abs_nonneg _) (by norm_num)
    _ = B := one_mul B

/-- `discSupShift` is nonnegative. -/
lemma discSupShift_nonneg (x q h : ℕ) (hx : 1 ≤ x) : 0 ≤ discSupShift x q h := by
  rw [discSupShift]
  rcases eq_or_ne q 0 with hq | hq
  · subst hq
    refine le_trans (abs_nonneg _) (le_csSup ?_ ⟨1, Nat.coprime_one_right 0, rfl⟩)
    refine ⟨|discShift (fun n => thetaNat n) x 0 1 h|, fun y hy => ?_⟩
    rcases hy with ⟨a, ha, rfl⟩
    have ha1 : a = 1 := by simpa using ha.gcd_eq_one
    subst ha1
    exact le_refl _
  · have hq1 : 1 ≤ q := by omega
    refine le_trans (abs_nonneg _) (le_csSup ?_ ⟨1, Nat.coprime_one_left q, rfl⟩)
    exact ⟨2 * (q.divisors.card : ℝ) * ((x : ℝ) / q + 2) * Real.log ((windowUp x h : ℕ) : ℝ),
      fun y hy => by rcases hy with ⟨a, _, rfl⟩; exact abs_discShift_theta_le x q a h hq1 hx⟩

/-- **Pointwise bound for a summand of `thetaDiscSum`.**  Using the primitive CRT
class, each summand is dominated by `BF^k·BG^k·discSupShift`. -/
lemma summand_le {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {x W b h wd D : ℕ} {H : Fin k → ℕ}
    (hx : 1 ≤ x) (hW2 : 2 ≤ W)
    (hWdiv : ∀ p : ℕ, Nat.Prime p → p ≤ wd → p ∣ W)
    (hbWh : (b + h).Coprime W) (hhne : ∀ i, h ≠ H i)
    (hseph : ∀ i, h - H i < wd ∧ H i - h < wd)
    (hQ : ∀ d e : Fin k → Fin (D + 1),
        coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0 →
        W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ≤ x)
    (d e : Fin k → Fin (D + 1)) :
    |goodInd W d e *
      (coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        discShift (fun n => thetaNat n) x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
          (classResidue x W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h)| ≤
      BF ^ k * BG ^ k *
        discSupShift x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h := by
  classical
  by_cases hg : lcmGood W d e
  · by_cases hco : coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
        (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) = 0
    · have hzero : goodInd W d e *
          (coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          discShift (fun n => thetaNat n) x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
            (classResidue x W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h) = 0 := by
        rw [hco]; ring
      rw [hzero, abs_zero]
      exact mul_nonneg (by positivity) (discSupShift_nonneg x _ h hx)
    · have hg' := hg
      rw [lcmGood] at hg'
      obtain ⟨hcW, hcm⟩ := hg'
      have hm0 : ∀ i : Fin k, 0 < Nat.lcm (d i : ℕ) (e i : ℕ) := by
        intro i
        rcases Nat.eq_zero_or_pos (Nat.lcm (d i : ℕ) (e i : ℕ)) with h0 | h0
        · exfalso
          have h1 := (hcW i).gcd_eq_one
          rw [h0, Nat.gcd_zero_left] at h1
          omega
        · exact h0
      have hq1 : 1 ≤ W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) := by
        have h2 : 0 < ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) :=
          Finset.prod_pos (fun i _ => hm0 i)
        exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) h2)
      have hcop := classResidue_coprime (N := x) (W := W) (b := b) (h := h) (wd := wd)
        (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ))
        (by omega) hm0 hcW hcm hWdiv hbWh hhne hseph (hQ d e hco)
      have hd := abs_discShift_le_discSupShift x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
        (classResidue x W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h hq1 hx hcop
      have hcoB : |coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ))| ≤ BF ^ k * BG ^ k := by
        rw [coefProd, Finset.abs_prod]
        calc ∏ i : Fin k, |lamDivWeight (F i) x (d i : ℕ) * lamDivWeight (G i) x (e i : ℕ)|
            ≤ ∏ _i : Fin k, BF * BG := by
              apply Finset.prod_le_prod₀
              · intro i _; positivity
              · intro i _; rw [abs_mul]
                exact mul_le_mul (abs_lamDivWeight_le hBF (hFbd i) x _)
                  (abs_lamDivWeight_le hBG (hGbd i) x _) (abs_nonneg _) hBF
          _ = (BF * BG) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = BF ^ k * BG ^ k := mul_pow _ _ _
      have hgi : goodInd W d e = 1 := by simp [goodInd, hg]
      rw [hgi, one_mul, abs_mul]
      calc |coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ))| *
            |discShift (fun n => thetaNat n) x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
              (classResidue x W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h|
          ≤ (BF ^ k * BG ^ k) *
              discSupShift x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h :=
            mul_le_mul hcoB hd (abs_nonneg _) (by positivity)
        _ = BF ^ k * BG ^ k *
              discSupShift x (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h := rfl
  · have hgi : goodInd W d e = 0 := by simp [goodInd, hg]
    rw [hgi, zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (discSupShift_nonneg x _ h hx)


/-- **Fibre-grouped bound for `thetaDiscSum`.**  Grouping the divisor pairs by
`∏ᵢ[dᵢ,eᵢ] ≤ Q` (the support restriction) and counting each fibre by
`τ(M)^{3k}`. -/
lemma thetaDiscSum_abs_le_fibre {k : ℕ} (hk : 1 ≤ k)
    {F G : Fin k → ℝ → ℝ} {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {x W b h wd D Q : ℕ} {H : Fin k → ℕ}
    (hx : 1 ≤ x) (hW2 : 2 ≤ W)
    (hWdiv : ∀ p : ℕ, Nat.Prime p → p ≤ wd → p ∣ W)
    (hbWh : (b + h).Coprime W) (hhne : ∀ i, h ≠ H i)
    (hseph : ∀ i, h - H i < wd ∧ H i - h < wd)
    (hQbd : ∀ d e : Fin k → Fin (D + 1),
        coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0 →
        (∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) ≤ Q)
    (hWQ : W * Q ≤ x) :
    |thetaDiscSum (N := x) (W := W) (b := b) (h := h) (D := D) H
      (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)| ≤
    BF ^ k * BG ^ k * ∑ M ∈ Finset.Icc 1 Q,
      ((M.divisors.card : ℝ)) ^ (3 * k) * discSupShift x (W * M) h := by
  classical
  set T : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) := Finset.univ with hT
  set cw : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) → ℝ := fun p =>
    coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
      (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) with hcw
  set mc : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) → ℕ := fun p =>
    ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) with hmc
  set term : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) → ℝ := fun p =>
    goodInd W p.1 p.2 * (cw p * discShift (fun n => thetaNat n) x (W * mc p)
      (classResidue x W b h H (fun i => Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ))) h) with hterm
  have htheta : thetaDiscSum (N := x) (W := W) (b := b) (h := h) (D := D) H
      (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) = ∑ p ∈ T, term p := by
    rw [hT, thetaDiscSum]
    conv_rhs => rw [Fintype.sum_prod_type (f := term)]
  rw [htheta]
  -- pointwise bound, with the `cw = 0` case handled
  have hstep2 : ∑ p ∈ T, |term p| ≤
      BF ^ k * BG ^ k * ∑ p ∈ T.filter (fun p => cw p ≠ 0),
        discSupShift x (W * mc p) h := by
    rw [Finset.mul_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : cw p ≠ 0
    · rw [if_pos hp]
      have hq : W * (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ x :=
        Nat.le_trans (Nat.mul_le_mul_left W (hQbd p.1 p.2 hp)) hWQ
      have := summand_le hk F G hBF hBG hFbd hGbd hx hW2 hWdiv hbWh hhne hseph
        (fun d e hco => Nat.le_trans (Nat.mul_le_mul_left W (hQbd d e hco)) hWQ) p.1 p.2
      simpa only [term, cw, mc] using this
    · rw [if_neg hp]
      have hp0 : cw p = 0 := not_not.mp hp
      have hz : term p = 0 := by
        simp only [term]
        rw [hp0]
        ring
      rw [hz, abs_zero]
  -- Step 5: fibre grouping
  have hfibre : ∀ p ∈ T.filter (fun p => cw p ≠ 0), mc p ∈ Finset.Icc 1 Q := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hne⟩ := hp
    have hne' : coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
        (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) ≠ 0 := hne
    rw [coefProd] at hne'
    have hd0 : ∀ i : Fin k, (p.1 i : ℕ) ≠ 0 ∧ (p.2 i : ℕ) ≠ 0 := by
      intro i
      have hf := (Finset.prod_ne_zero_iff.mp hne') i (Finset.mem_univ i)
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hf
      exact ⟨fun h0 => h1 (by simp [lamDivWeight, moebiusReal, h0]),
        fun h0 => h2 (by simp [lamDivWeight, moebiusReal, h0])⟩
    have hpos : 0 < mc p := by
      rw [hmc]
      exact Finset.prod_pos fun i _ =>
        Nat.lcm_pos (Nat.pos_of_ne_zero (hd0 i).1) (Nat.pos_of_ne_zero (hd0 i).2)
    have hle : mc p ≤ Q := by
      rw [hmc]; exact hQbd p.1 p.2 hne
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have hstep5 : ∑ p ∈ T.filter (fun p => cw p ≠ 0), discSupShift x (W * mc p) h ≤
      ∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (3 * k) * discSupShift x (W * M) h := by
    have hfib := Finset.sum_fiberwise_of_maps_to hfibre
      (f := fun p => discSupShift x (W * mc p) h)
    rw [← hfib]
    refine Finset.sum_le_sum fun M hM => ?_
    rw [Finset.mem_Icc] at hM
    have hM0 : M ≠ 0 := by omega
    have hconst : ∑ i ∈ (T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M),
          discSupShift x (W * mc i) h =
        ((((T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M)).card : ℝ) *
          discSupShift x (W * M) h) := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
        Finset.sum_const, nsmul_eq_mul]
    have hcount : (((T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M)).card : ℝ) ≤
        (((M.divisors.card) ^ (3 * k) : ℕ) : ℝ) := by
      have hsub : (T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M) ⊆
          (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
            (fun p => (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨Finset.mem_univ _, by simpa only [hmc] using hp.2⟩
      have h1 : ((T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M)).card ≤
          ((Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
            (fun p => (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M)).card :=
        Finset.card_le_card hsub
      have h2 : ((Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
            (fun p => (∏ i : Fin k, ((p.1 i : ℕ)).lcm ((p.2 i : ℕ))) = M)).card ≤
          (M.divisors.card) ^ (3 * k) :=
        Commons.NumberTheory.ArithmeticFunction.card_fibre_prod_lcm_le k D M hM0
      exact_mod_cast le_trans h1 h2
    have hA0 : 0 ≤ discSupShift x (W * M) h := discSupShift_nonneg x _ h hx
    rw [hconst]
    calc (((T.filter (fun p => cw p ≠ 0)).filter (fun p => mc p = M)).card : ℝ) *
          discSupShift x (W * M) h
        ≤ (((M.divisors.card) ^ (3 * k) : ℕ) : ℝ) * discSupShift x (W * M) h :=
          mul_le_mul_of_nonneg_right hcount hA0
      _ = ((M.divisors.card : ℝ)) ^ (3 * k) * discSupShift x (W * M) h := by
          rw [Nat.cast_pow]
  calc |∑ p ∈ T, term p|
      ≤ ∑ p ∈ T, |term p| := Finset.abs_sum_le_sum_abs term T
    _ ≤ BF ^ k * BG ^ k * ∑ p ∈ T.filter (fun p => cw p ≠ 0),
        discSupShift x (W * mc p) h := hstep2
    _ ≤ BF ^ k * BG ^ k * ∑ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (3 * k) * discSupShift x (W * M) h :=
        mul_le_mul_of_nonneg_left hstep5 (by positivity)

/-- The level-of-distribution sum in the integer-exponent form. -/
lemma lod_sum_le_nat {ϑ : ℝ} (hlev : levelOfDistribution ϑ) (n : ℕ) (hn : 1 ≤ n) (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ, (Q : ℝ) ≤ (x : ℝ) ^ ϑ →
      (∑ q ∈ Finset.Icc 1 Q,
        (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
          (fun h' => discSupShift x q h')) ≤
        (x : ℝ) / (Real.log (x : ℝ)) ^ n := by
  have h1 := hlev (n : ℝ) (by exact_mod_cast hn) h
  have h2 : ∀ᶠ x : ℕ in atTop, 1 ≤ x := eventually_ge_atTop 1
  refine (h1.and h2).mono fun x hx => ?_
  obtain ⟨hx1, hx2⟩ := hx
  intro Q hQ
  have hlog0 : (0 : ℝ) ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx2)
  refine le_trans (hx1 Q hQ) (le_of_eq ?_)
  rw [Real.rpow_neg hlog0, Real.rpow_natCast, inv_eq_one_div, mul_one_div]

/-- **Cauchy--Schwarz for the fibre sum.** -/
lemma fibre_cauchy {k : ℕ} {s : Finset ℕ} {Aq : ℕ → ℝ} (hA : ∀ M ∈ s, 0 ≤ Aq M) :
    (∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (3 * k) * Aq M) ≤
      Real.sqrt (∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (6 * k) * Aq M) *
      Real.sqrt (∑ M ∈ s, Aq M) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun M => ((M.divisors.card : ℝ)) ^ (3 * k) * Real.sqrt (Aq M))
    (fun M => Real.sqrt (Aq M))
  have hsum : (∑ M ∈ s,
        (((M.divisors.card : ℝ)) ^ (3 * k) * Real.sqrt (Aq M)) * Real.sqrt (Aq M)) =
      ∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (3 * k) * Aq M := by
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [mul_assoc, Real.mul_self_sqrt (hA M hM)]
  have hsq1 : (∑ M ∈ s, (((M.divisors.card : ℝ)) ^ (3 * k) * Real.sqrt (Aq M)) ^ 2) =
      ∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (6 * k) * Aq M := by
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [mul_pow, ← pow_mul, Real.sq_sqrt (hA M hM), show 3 * k * 2 = 6 * k by ring]
  have hsq2 : (∑ M ∈ s, (Real.sqrt (Aq M)) ^ 2) = ∑ M ∈ s, Aq M := by
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [Real.sq_sqrt (hA M hM)]
  rw [hsum, hsq1, hsq2] at h1
  have hX0 : (0 : ℝ) ≤ ∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (6 * k) * Aq M :=
    Finset.sum_nonneg fun M hM => mul_nonneg (by positivity) (hA M hM)
  have hY0 : (0 : ℝ) ≤ ∑ M ∈ s, Aq M := Finset.sum_nonneg hA
  have hL0 : (0 : ℝ) ≤ ∑ M ∈ s, ((M.divisors.card : ℝ)) ^ (3 * k) * Aq M :=
    Finset.sum_nonneg fun M hM => mul_nonneg (by positivity) (hA M hM)
  have h2 := (Real.le_sqrt hL0 (mul_nonneg hX0 hY0)).mpr h1
  rw [Real.sqrt_mul hX0] at h2
  exact h2


/-! ## The final assembly -/

/-- `C·x^a ≤ x^b` eventually, for `a < b` and `C ≥ 0`. -/
lemma eventually_const_mul_rpow_le {C a b : ℝ} (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ x : ℕ in atTop, C * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
  rcases eq_or_lt_of_le hC with h0 | hpos
  · filter_upwards [eventually_ge_atTop 1] with x _
    rw [← h0, zero_mul]
    exact Real.rpow_nonneg (by positivity) b
  · have hb : 0 < b - a := by linarith
    have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (b - a)) atTop atTop :=
      (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1]
      with x hx hx1
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
    calc C * (x : ℝ) ^ a ≤ (x : ℝ) ^ (b - a) * (x : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (by positivity) a)
      _ = (x : ℝ) ^ ((b - a) + a) := (Real.rpow_add hxpos _ _).symm
      _ = (x : ℝ) ^ b := by rw [show b - a + a = b by ring]

/-- `log (2x + h + 1) ≤ 2 log x` eventually. -/
lemma eventually_log_window_le (h : ℕ) :
    ∀ᶠ x : ℕ in atTop, Real.log ((windowUp x h : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  filter_upwards [eventually_ge_atTop (max (h + 1) 4)] with x hx
  have hx3 : 3 ≤ x := by
    have := le_trans (le_max_right (h + 1) 4) hx; omega
  have hxh : h + 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hw : ((windowUp x h : ℕ) : ℝ) ≤ 3 * (x : ℝ) := by
    have : windowUp x h ≤ 3 * x := by show 2 * x + h + 1 ≤ 3 * x; omega
    exact_mod_cast this
  have hwpos : (0 : ℝ) < ((windowUp x h : ℕ) : ℝ) := by
    have hnat : 0 < windowUp x h := by unfold windowUp; omega
    exact_mod_cast hnat
  have h1 : Real.log ((windowUp x h : ℕ) : ℝ) ≤ Real.log (3 * (x : ℝ)) :=
    Real.log_le_log hwpos hw
  rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)] at h1
  have h2 : Real.log 3 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hx3)
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  linarith

/-- `log ⌈x^ϑ'⌉ + 1 ≤ 2 log x` eventually, for `0 ≤ ϑ' < 1`. -/
lemma eventually_log_ceil_le {ϑ' : ℝ} (h0 : 0 ≤ ϑ') (h1 : ϑ' < 1) :
    ∀ᶠ x : ℕ in atTop,
      Real.log ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by
  have hlim : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop := tendsto_log_nat_atTop
  have hpos : 0 < 1 - ϑ' := by linarith
  filter_upwards [hlim.eventually (eventually_ge_atTop ((Real.log 2 + 1) / (1 - ϑ'))),
    eventually_ge_atTop 2] with x hx hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have h1x : (1 : ℝ) ≤ (x : ℝ) ^ ϑ' := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) h0
  have hceil : ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) ≤ 2 * (x : ℝ) ^ ϑ' := by
    have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg x) ϑ')
    have h2 : (1 : ℝ) ≤ (x : ℝ) ^ ϑ' := h1x
    linarith
  have hceilpos : (0 : ℝ) < ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) (le_trans h1x (Nat.le_ceil _))
  have hstep : Real.log ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) ≤
      Real.log 2 + ϑ' * Real.log (x : ℝ) := by
    calc Real.log ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) ≤ Real.log (2 * (x : ℝ) ^ ϑ') :=
          Real.log_le_log hceilpos hceil
      _ = Real.log 2 + Real.log ((x : ℝ) ^ ϑ') :=
          Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hxpos ϑ'))
      _ = Real.log 2 + ϑ' * Real.log (x : ℝ) := by rw [Real.log_rpow hxpos]
  have hkey : Real.log 2 + 1 ≤ (1 - ϑ') * Real.log (x : ℝ) := by
    have := mul_le_mul_of_nonneg_left hx hpos.le
    rw [mul_comm (1 - ϑ') _, div_mul_cancel₀ _ (ne_of_gt hpos)] at this
    exact this
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  linarith


/-! ## The numeric assembly of P8 (46) -/

/-- **Polymath8a (46): the discrepancy part of Theorem 3.5(i).**  For a family of
moduli `Wf` (every prime `≤ w x → ∞` divides `Wf x`, `log Wf = o(√log x)`) and
shifts separated by `wd`, the discrepancy part `thetaDiscSum` of the θ-weighted
window expansion is `O(x · log^{-B} x)` for every fixed `B`, using only the
level-of-distribution input `levelOfDistribution ϑ` and the divisor-sum bound
`Σ_{M ≤ Q} τ(M)^{6k+1}/φ(M) ≪ (log Q)^{2^{6k+3}}`. -/
theorem thetaDiscSum_le {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {Mf Mg : Fin k → ℝ} (hMfnn : ∀ i, 0 ≤ Mf i) (hMgnn : ∀ i, 0 ≤ Mg i)
    (hMf : ∀ (i : Fin k) (t : ℝ), Mf i < |t| → F i t = 0)
    (hMg : ∀ (i : Fin k) (t : ℝ), Mg i < |t| → G i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ2 : ϑ < 1 / 2) (hsum : ∑ i, (Mf i + Mg i) < ϑ)
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ => Real.log (Wf x) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (b : ℕ → ℕ) (h : ℕ) (H : Fin k → ℕ)
    (hbWh : ∀ᶠ x : ℕ in atTop, (b x + h).Coprime (Wf x)) (hhne : ∀ i, h ≠ H i)
    (wd : ℕ → ℕ) (hwdw : ∀ᶠ x : ℕ in atTop, wd x ≤ w x)
    (hseph : ∀ᶠ x : ℕ in atTop, ∀ i, h - H i < wd x ∧ H i - h < wd x)
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (Wf x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (D : ℕ → ℕ) (Bexp : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      |thetaDiscSum (N := x) (W := Wf x) (b := b x) (h := h) (D := D x) H
        (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)|
        ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ Bexp := by
  classical
  -- ===== setup =====
  set ϑ' : ℝ := ∑ i, (Mf i + Mg i) with hϑ'def
  have hϑ'nn : 0 ≤ ϑ' := by
    rw [hϑ'def]
    exact Finset.sum_nonneg fun i _ => add_nonneg (hMfnn i) (hMgnn i)
  have hϑ'lt : ϑ' < ϑ := by rw [hϑ'def]; exact hsum
  have hϑ'lt1 : ϑ' < 1 := by linarith
  set cc : ℝ := (ϑ - ϑ') / 2 with hccdef
  have hccpos : 0 < cc := by rw [hccdef]; linarith
  have hcclt : cc + ϑ' < ϑ := by rw [hccdef]; linarith
  have hcclt1 : cc + ϑ' < 1 := by linarith
  obtain ⟨Cdiv, hCdivpos, hCdiv⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform
      (2 * k + 1)
  set e₁ : ℕ := 2 ^ (3 * (2 * k + 1)) with he₁def
  have he₁eq : e₁ = 2 ^ (6 * k + 3) := by rw [he₁def]; congr 1; ring
  set Alev : ℕ := e₁ + 1 + 2 * Bexp with hAlevdef
  have hAlev1 : 1 ≤ Alev := by
    rw [hAlevdef]
    exact le_trans (Nat.succ_le_succ (Nat.zero_le e₁)) (Nat.le_add_right _ _)
  -- ===== eventual facts =====
  have hw2 : ∀ᶠ x : ℕ in atTop, 2 ≤ w x := hw.eventually (eventually_ge_atTop 2)
  have hW2 : ∀ᶠ x : ℕ in atTop, 2 ≤ Wf x := by
    filter_upwards [hw2] with x hx
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (hW x)) (hsmall x 2 Nat.prime_two hx)
  have hx2 : ∀ᶠ x : ℕ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hlg1 : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)
  have hWcc : ∀ᶠ x : ℕ in atTop, (Wf x : ℝ) ≤ (x : ℝ) ^ cc :=
    eventually_le_rpow_of_log_ratio' hW hccpos hlq
  have h4xϑ : ∀ᶠ x : ℕ in atTop, 4 * (x : ℝ) ^ (cc + ϑ') ≤ (x : ℝ) ^ ϑ :=
    eventually_const_mul_rpow_le (C := 4) (by norm_num) hcclt
  have h4x1 : ∀ᶠ x : ℕ in atTop, 4 * (x : ℝ) ^ (cc + ϑ') ≤ (x : ℝ) ^ (1 : ℝ) :=
    eventually_const_mul_rpow_le (C := 4) (by norm_num) hcclt1
  have hLw : ∀ᶠ x : ℕ in atTop,
      Real.log ((windowUp x h : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := eventually_log_window_le h
  have hLc : ∀ᶠ x : ℕ in atTop,
      Real.log ((Nat.ceil ((x : ℝ) ^ ϑ') : ℕ) : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) :=
    eventually_log_ceil_le hϑ'nn hϑ'lt1
  have hlev' := lod_sum_le_nat hlev Alev hAlev1 h
  -- ===== the constant =====
  refine ⟨max 1 (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)), ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  filter_upwards [hW2, hx2, hlg1, hWcc, h4xϑ, h4x1, hLw, hLc, hlev', hbWh, hwdw, hseph]
    with x hW2x hx2x hlg1x hWccx h4xϑx h4x1x hLwx hLcx hlevx hbWhx hwdwx hsephx
  set xr : ℝ := (x : ℝ) with hxr_def
  set Wr : ℝ := (Wf x : ℝ) with hWr_def
  set lg : ℝ := Real.log (x : ℝ) with hlg_def
  set L : ℝ := Real.log ((windowUp x h : ℕ) : ℝ) with hL_def
  set Q : ℕ := Nat.ceil (xr ^ ϑ') with hQdef
  -- basic facts
  have hx1x : 1 ≤ x := by omega
  have hxpos : (0 : ℝ) < xr := by rw [hxr_def]; exact_mod_cast (by omega : 0 < x)
  have hxrnn : 0 ≤ xr := le_of_lt hxpos
  have hlgpos : 0 < lg := lt_of_lt_of_le zero_lt_one hlg1x
  have hWrpos : 0 < Wr := by rw [hWr_def]; exact_mod_cast (Nat.pos_of_ne_zero (hW x))
  have hWrnn : 0 ≤ Wr := le_of_lt hWrpos
  have hWr1 : 1 ≤ Wr := by rw [hWr_def]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hW x))
  have hLnn : 0 ≤ L := by
    rw [hL_def]
    exact Real.log_nonneg (by
      show (1 : ℝ) ≤ ((windowUp x h : ℕ) : ℝ)
      exact_mod_cast (by show 1 ≤ 2 * x + h + 1; omega))
  have hQpow1 : 1 ≤ xr ^ ϑ' := by
    rw [hxr_def]
    exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) hϑ'nn
  have hQge1 : 1 ≤ Q := by
    rw [hQdef]
    have h0 : ((1 : ℕ) : ℝ) ≤ xr ^ ϑ' := by simpa using hQpow1
    have h1 : ((1 : ℕ) : ℝ) ≤ ((Nat.ceil (xr ^ ϑ') : ℕ) : ℝ) :=
      le_trans h0 (Nat.le_ceil _)
    exact_mod_cast h1
  have hQceil : xr ^ ϑ' ≤ (Q : ℝ) := by rw [hQdef]; exact Nat.le_ceil _
  have hQle : (Q : ℝ) ≤ 2 * xr ^ ϑ' := by
    rw [hQdef]
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hxrnn ϑ')
    linarith
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hlgQ0 : 0 ≤ Real.log (Q : ℝ) + 1 := by
    have h1 : 1 ≤ (Q : ℝ) := by exact_mod_cast hQge1
    have := Real.log_nonneg h1
    linarith
  -- ===== the X-side divisor sums =====
  set Kd : ℝ := Cdiv * (Real.log (Q : ℝ) + 1) ^ e₁ with hKddef
  have hKdnn : 0 ≤ Kd := by rw [hKddef]; positivity
  have hT1 : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) ≤ Kd := by
    have hstep : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) ≤
        ∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 3) / (M.totient : ℝ) := by
      refine Finset.sum_le_sum fun M hM => ?_
      obtain ⟨hM1, hMQ⟩ := Finset.mem_Icc.mp hM
      have hτ1 : (1 : ℝ) ≤ ((M.divisors.card : ℝ)) := by
        have hmem : (1 : ℕ) ∈ M.divisors :=
          Nat.mem_divisors.mpr ⟨one_dvd M, by omega⟩
        have hcard : 1 ≤ M.divisors.card := Finset.card_pos.mpr ⟨1, hmem⟩
        exact_mod_cast hcard
      have hpow : ((M.divisors.card : ℝ)) ^ (6 * k + 1) ≤
          ((M.divisors.card : ℝ)) ^ (6 * k + 3) :=
        pow_le_pow_right₀ hτ1 (by omega)
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      have hφpos : (0 : ℝ) < (M.totient : ℝ) := by
        exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < M))
      have hφle : (M.totient : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
      calc ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)
          ≤ ((M.divisors.card : ℝ)) ^ (6 * k + 3) / (M : ℝ) :=
            div_le_div_of_nonneg_right hpow (le_of_lt hMpos)
        _ ≤ ((M.divisors.card : ℝ)) ^ (6 * k + 3) / (M.totient : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hφpos hφle
    have h2 := hCdiv Q
    rw [show 3 * (2 * k + 1) = 6 * k + 3 by ring] at h2
    refine le_trans hstep ?_
    rw [hKddef]
    exact h2
  have hT2 : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1)) ≤
      (Q : ℝ) * Kd := by
    have hstep : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1)) ≤
        ∑ M ∈ Finset.Icc 1 Q, (Q : ℝ) *
          (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) := by
      refine Finset.sum_le_sum fun M hM => ?_
      obtain ⟨hM1, hMQ⟩ := Finset.mem_Icc.mp hM
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      have hcast : (M : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hMQ
      calc ((M.divisors.card : ℝ)) ^ (6 * k + 1)
          = (M : ℝ) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) := by
            field_simp
        _ ≤ (Q : ℝ) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
    rw [← Finset.mul_sum] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hT1 hQnn)
  -- ===== the kernel comparison =====
  have hKd : Kd ≤ Cdiv * 2 ^ e₁ * lg ^ e₁ := by
    rw [hKddef]
    have h1 : (Real.log (Q : ℝ) + 1) ^ e₁ ≤ (2 * lg) ^ e₁ :=
      pow_le_pow_left₀ hlgQ0 hLcx e₁
    calc Cdiv * (Real.log (Q : ℝ) + 1) ^ e₁ ≤ Cdiv * (2 * lg) ^ e₁ :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hCdivpos)
      _ = Cdiv * 2 ^ e₁ * lg ^ e₁ := by rw [mul_pow]; ring
  have hτW : ((Wf x).divisors.card : ℝ) ≤ Wr := by
    rw [hWr_def]
    exact_mod_cast Nat.card_divisors_le_self (Wf x)
  have hWQmid : Wr * (Q : ℝ) ≤ 2 * xr ^ (cc + ϑ') := by
    calc Wr * (Q : ℝ) ≤ xr ^ cc * (2 * xr ^ ϑ') :=
          mul_le_mul hWccx hQle (by positivity) (Real.rpow_nonneg hxrnn cc)
      _ = 2 * xr ^ (cc + ϑ') := by rw [Real.rpow_add hxpos]; ring
  have hxpowcc : (0 : ℝ) ≤ xr ^ (cc + ϑ') := Real.rpow_nonneg hxrnn _
  have hmidpow : 2 * xr ^ (cc + ϑ') ≤ 4 * xr ^ (cc + ϑ') :=
    mul_le_mul_of_nonneg_right (by norm_num) hxpowcc
  have hWQx : Wf x * Q ≤ x := by
    have h2 : ((Wf x * Q : ℕ) : ℝ) ≤ 2 * xr ^ (cc + ϑ') := by
      rw [Nat.cast_mul, ← hWr_def]; exact hWQmid
    have h3 : 4 * xr ^ (cc + ϑ') ≤ xr := by
      have h4 := h4x1x
      rwa [Real.rpow_one] at h4
    have h1 : ((Wf x * Q : ℕ) : ℝ) ≤ xr := le_trans h2 (le_trans hmidpow h3)
    rw [hxr_def] at h1
    exact_mod_cast h1
  have hQle' : ((Wf x * Q : ℕ) : ℝ) ≤ xr ^ ϑ := by
    have h2 : ((Wf x * Q : ℕ) : ℝ) ≤ 2 * xr ^ (cc + ϑ') := by
      rw [Nat.cast_mul, ← hWr_def]; exact hWQmid
    exact le_trans h2 (le_trans hmidpow h4xϑx)
  -- ===== the fibre bound =====
  have hQbd : ∀ d e : Fin k → Fin (D x + 1),
      coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
        (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0 →
      (∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) ≤ Q := by
    intro d e hne
    have h := lcm_prod_le_of_coefProd_ne_zero (D := D x) F G x (by omega) hMf hMg
      (ϑ := ϑ') (Q := (Q : ℝ)) (le_of_eq hϑ'def.symm) hQceil hne
    exact_mod_cast h
  have hwdx : ∀ p : ℕ, Nat.Prime p → p ≤ wd x → p ∣ Wf x :=
    fun p hp hpw => hsmall x p hp (le_trans hpw hwdwx)
  have hfib := thetaDiscSum_abs_le_fibre (k := k) hk (F := F) (G := G) hBF hBG hFbd hGbd
    (x := x) (W := Wf x) (b := b x) (h := h) (wd := wd x) (D := D x) (Q := Q) (H := H)
    hx1x hW2x hwdx hbWhx hhne hsephx hQbd hWQx
  -- ===== Cauchy--Schwarz =====
  have hAq : ∀ M ∈ Finset.Icc 1 Q, 0 ≤ discSupShift x (Wf x * M) h :=
    fun M _ => discSupShift_nonneg x _ h hx1x
  have hcs := fibre_cauchy (k := k) (s := Finset.Icc 1 Q)
    (Aq := fun M => discSupShift x (Wf x * M) h) hAq
  -- ===== the X-core bound =====
  have hXcore : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k) *
      discSupShift x (Wf x * M) h) ≤
      2 * L * ((Wf x).divisors.card : ℝ) *
        ((xr / Wr) * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ))
          + 2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1))) := by
    have hpt : ∀ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (6 * k) * discSupShift x (Wf x * M) h ≤
        2 * L * ((Wf x).divisors.card : ℝ) *
          ((xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) +
            2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1)) := by
      intro M hM
      obtain ⟨hM1, hMQ⟩ := Finset.mem_Icc.mp hM
      have hM0 : M ≠ 0 := by omega
      have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      have hWM1 : 1 ≤ Wf x * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hW x) hM0)
      have hcrude := discSupShift_le_crude x (Wf x * M) h hWM1 hx1x
      have hτWM : (((Wf x * M).divisors.card : ℝ)) ≤
          ((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ)) := by
        have h := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le (Wf x) M
        exact_mod_cast h
      have hxM : xr / ((Wf x * M : ℕ) : ℝ) = (xr / Wr) * (1 / (M : ℝ)) := by
        rw [Nat.cast_mul, ← hWr_def, ← div_div, div_eq_mul_one_div]
      have hR2 : (0 : ℝ) ≤ xr / ((Wf x * M : ℕ) : ℝ) + 2 := by
        have := div_nonneg hxrnn (Nat.cast_nonneg (Wf x * M)); linarith
      have hτM0 : (0 : ℝ) ≤ ((M.divisors.card : ℝ)) ^ (6 * k) := by positivity
      have h1 : 2 * (((Wf x * M).divisors.card : ℝ)) ≤
          2 * (((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hτWM (by norm_num)
      have h2 : 2 * (((Wf x * M).divisors.card : ℝ)) *
            (xr / ((Wf x * M : ℕ) : ℝ) + 2) ≤
          2 * (((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ))) *
            (xr / ((Wf x * M : ℕ) : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right h1 hR2
      have h3 : 2 * (((Wf x * M).divisors.card : ℝ)) *
            (xr / ((Wf x * M : ℕ) : ℝ) + 2) * L ≤
          2 * (((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ))) *
            (xr / ((Wf x * M : ℕ) : ℝ) + 2) * L :=
        mul_le_mul_of_nonneg_right h2 hLnn
      have h4 := mul_le_mul_of_nonneg_left h3 hτM0
      have h5 := mul_le_mul_of_nonneg_left hcrude hτM0
      have h6 : 2 * (((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ))) *
            (xr / ((Wf x * M : ℕ) : ℝ) + 2) * L *
              ((M.divisors.card : ℝ)) ^ (6 * k) =
          2 * L * ((Wf x).divisors.card : ℝ) *
            ((xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) +
              2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1)) := by
        rw [hxM]; ring
      calc ((M.divisors.card : ℝ)) ^ (6 * k) * discSupShift x (Wf x * M) h
          = ((M.divisors.card : ℝ)) ^ (6 * k) *
              discSupShift x (Wf x * M) h := rfl
        _ ≤ ((M.divisors.card : ℝ)) ^ (6 * k) *
              (2 * (((Wf x * M).divisors.card : ℝ)) *
                (xr / ((Wf x * M : ℕ) : ℝ) + 2) * L) := h5
        _ ≤ ((M.divisors.card : ℝ)) ^ (6 * k) *
              (2 * (((Wf x).divisors.card : ℝ) * ((M.divisors.card : ℝ))) *
                (xr / ((Wf x * M : ℕ) : ℝ) + 2) * L) := h4
        _ = 2 * L * ((Wf x).divisors.card : ℝ) *
              ((xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) +
                2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1)) := by
            rw [← h6]; ring
    calc (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k) *
            discSupShift x (Wf x * M) h)
        ≤ ∑ M ∈ Finset.Icc 1 Q, 2 * L * ((Wf x).divisors.card : ℝ) *
            ((xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) +
              2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1)) :=
          Finset.sum_le_sum hpt
      _ = 2 * L * ((Wf x).divisors.card : ℝ) *
            (∑ M ∈ Finset.Icc 1 Q,
              ((xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) +
                2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1))) := by
          simp only [Finset.mul_sum]
      _ = 2 * L * ((Wf x).divisors.card : ℝ) *
            ((∑ M ∈ Finset.Icc 1 Q,
                (xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)))
              + (∑ M ∈ Finset.Icc 1 Q, 2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1))) := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * L * ((Wf x).divisors.card : ℝ) *
            ((xr / Wr) * (∑ M ∈ Finset.Icc 1 Q,
                ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ))
              + 2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1))) := by
          rw [show (∑ M ∈ Finset.Icc 1 Q,
                (xr / Wr) * (((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ))) =
              (xr / Wr) * (∑ M ∈ Finset.Icc 1 Q,
                ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) from by
                  simp only [Finset.mul_sum],
            show (∑ M ∈ Finset.Icc 1 Q, 2 * ((M.divisors.card : ℝ)) ^ (6 * k + 1)) =
              2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1)) from by
                simp only [Finset.mul_sum]]
  -- ===== the Y-bound (level of distribution) =====
  have hY : (∑ M ∈ Finset.Icc 1 Q, discSupShift x (Wf x * M) h) ≤ xr / lg ^ Alev := by
    have hinj : ∀ M ∈ Finset.Icc 1 Q, ∀ M' ∈ Finset.Icc 1 Q,
        Wf x * M = Wf x * M' → M = M' := by
      intro M _ M' _ hEq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hW x)) hEq
    have himg : (∑ M ∈ Finset.Icc 1 Q,
          (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
            (fun h' => discSupShift x (Wf x * M) h')) =
        ∑ q ∈ (Finset.Icc 1 Q).image (fun M => Wf x * M),
          (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
            (fun h' => discSupShift x q h') := by
      rw [Finset.sum_image]
      intro M hM M' hM' hEq
      exact hinj M hM M' hM' hEq
    have hsub : (Finset.Icc 1 Q).image (fun M => Wf x * M) ⊆ Finset.Icc 1 (Wf x * Q) := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨M, hM, rfl⟩ := hq
      obtain ⟨hM1, hMQ⟩ := Finset.mem_Icc.mp hM
      exact Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hW x) (by omega)),
          Nat.mul_le_mul_left _ hMQ⟩
    have hnonneg : ∀ q ∈ Finset.Icc 1 (Wf x * Q),
        q ∉ (Finset.Icc 1 Q).image (fun M => Wf x * M) →
        (0 : ℝ) ≤ (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
          (fun h' => discSupShift x q h') := by
      intro q _ _
      exact le_trans (discSupShift_nonneg x q h hx1x) (discSupShift_le_lodSup x q h)
    calc (∑ M ∈ Finset.Icc 1 Q, discSupShift x (Wf x * M) h)
        ≤ ∑ M ∈ Finset.Icc 1 Q,
            (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
              (fun h' => discSupShift x (Wf x * M) h') :=
          Finset.sum_le_sum fun M _ => discSupShift_le_lodSup x (Wf x * M) h
      _ = ∑ q ∈ (Finset.Icc 1 Q).image (fun M => Wf x * M),
            (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
              (fun h' => discSupShift x q h') := himg
      _ ≤ ∑ q ∈ Finset.Icc 1 (Wf x * Q),
            (Finset.range (h + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos h)⟩
              (fun h' => discSupShift x q h') :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      _ ≤ xr / lg ^ Alev := hlevx (Wf x * Q) hQle'
  -- ===== the X-bound =====
  have hX : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k) *
      discSupShift x (Wf x * M) h) ≤ 8 * Cdiv * 2 ^ e₁ * xr * lg ^ (e₁ + 1) := by
    have hA1 : (xr / Wr) * (∑ M ∈ Finset.Icc 1 Q,
            ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ))
          + 2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1)) ≤
        Kd * (xr / Wr + 2 * (Q : ℝ)) := by
      have h1 : (xr / Wr) * (∑ M ∈ Finset.Icc 1 Q,
          ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ)) ≤ (xr / Wr) * Kd :=
        mul_le_mul_of_nonneg_left hT1 (div_nonneg hxrnn hWrnn)
      have h2 : 2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1)) ≤
          2 * ((Q : ℝ) * Kd) := mul_le_mul_of_nonneg_left hT2 (by norm_num)
      linarith [h1, h2]
    have hτWterm : ((Wf x).divisors.card : ℝ) * (xr / Wr + 2 * (Q : ℝ)) ≤ 2 * xr := by
      have hA : ((Wf x).divisors.card : ℝ) * (xr / Wr) ≤ xr := by
        have hle : ((Wf x).divisors.card : ℝ) / Wr ≤ 1 := by
          rw [div_le_one hWrpos]; exact hτW
        calc ((Wf x).divisors.card : ℝ) * (xr / Wr)
            = (((Wf x).divisors.card : ℝ) / Wr) * xr := by ring
          _ ≤ 1 * xr := mul_le_mul_of_nonneg_right hle hxrnn
          _ = xr := one_mul xr
      have hB : ((Wf x).divisors.card : ℝ) * (2 * (Q : ℝ)) ≤ xr := by
        have h3 : Wr * (2 * (Q : ℝ)) ≤ 4 * xr ^ (cc + ϑ') := by linarith [hWQmid]
        have h5 : 4 * xr ^ (cc + ϑ') ≤ xr := by
          have h4 := h4x1x
          rwa [Real.rpow_one] at h4
        calc ((Wf x).divisors.card : ℝ) * (2 * (Q : ℝ)) ≤ Wr * (2 * (Q : ℝ)) :=
              mul_le_mul_of_nonneg_right hτW (by positivity)
          _ ≤ 4 * xr ^ (cc + ϑ') := h3
          _ ≤ xr := h5
      linarith [hA, hB]
    calc (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k) *
            discSupShift x (Wf x * M) h)
        ≤ 2 * L * ((Wf x).divisors.card : ℝ) *
            ((xr / Wr) * (∑ M ∈ Finset.Icc 1 Q,
                ((M.divisors.card : ℝ)) ^ (6 * k + 1) / (M : ℝ))
              + 2 * (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (6 * k + 1))) := hXcore
      _ ≤ 2 * L * ((Wf x).divisors.card : ℝ) * (Kd * (xr / Wr + 2 * (Q : ℝ))) :=
          mul_le_mul_of_nonneg_left hA1 (by positivity)
      _ = 2 * L * Kd * (((Wf x).divisors.card : ℝ) * (xr / Wr + 2 * (Q : ℝ))) := by ring
      _ ≤ 2 * L * Kd * (2 * xr) := mul_le_mul_of_nonneg_left hτWterm (by positivity)
      _ = 4 * L * Kd * xr := by ring
      _ ≤ 4 * L * (Cdiv * 2 ^ e₁ * lg ^ e₁) * xr := by
          have hc : (0 : ℝ) ≤ 4 * L * xr := by positivity
          have := mul_le_mul_of_nonneg_right hKd hc
          linarith [this]
      _ = 4 * L * Cdiv * 2 ^ e₁ * lg ^ e₁ * xr := by ring
      _ ≤ 4 * (2 * lg) * Cdiv * 2 ^ e₁ * lg ^ e₁ * xr := by
          have hc : (0 : ℝ) ≤ 4 * Cdiv * 2 ^ e₁ * lg ^ e₁ * xr := by positivity
          have := mul_le_mul_of_nonneg_right hLwx hc
          linarith [this]
      _ = 8 * Cdiv * 2 ^ e₁ * xr * lg ^ (e₁ + 1) := by ring
  -- ===== the algebra for the square roots =====
  have hAlev_eq : Alev = e₁ + 1 + 2 * Bexp := hAlevdef
  have halgebra : 8 * Cdiv * 2 ^ e₁ * xr * lg ^ (e₁ + 1) * (xr / lg ^ Alev) =
      8 * Cdiv * 2 ^ e₁ * (xr / lg ^ Bexp) ^ 2 := by
    have hA : lg ^ Alev = lg ^ (e₁ + 1) * lg ^ (2 * Bexp) := by
      rw [hAlevdef, pow_add]
    have hB1 : lg ^ (2 * Bexp) = (lg ^ Bexp) ^ 2 := by
      rw [← pow_mul lg Bexp 2, Nat.mul_comm Bexp 2]
    rw [hA, hB1]
    field_simp <;> ring_nf
  have hsqrt : Real.sqrt (8 * Cdiv * 2 ^ e₁ * xr * lg ^ (e₁ + 1)) *
        Real.sqrt (xr / lg ^ Alev) = Real.sqrt (8 * Cdiv * 2 ^ e₁) * xr / lg ^ Bexp := by
    rw [← Real.sqrt_mul (by positivity), halgebra, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  -- ===== final assembly =====
  have hXY : (∑ M ∈ Finset.Icc 1 Q, ((M.divisors.card : ℝ)) ^ (3 * k) *
      discSupShift x (Wf x * M) h) ≤ Real.sqrt (8 * Cdiv * 2 ^ e₁) * xr / lg ^ Bexp := by
    refine le_trans hcs ?_
    refine le_trans (mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
    rw [hsqrt]
  have hfinal : |thetaDiscSum (N := x) (W := Wf x) (b := b x) (h := h) (D := D x) H
        (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)| ≤
      max 1 (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)) * xr / lg ^ Bexp := by
    refine le_trans hfib ?_
    refine le_trans (mul_le_mul_of_nonneg_left hXY (by positivity)) ?_
    have hm : BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁) ≤
        max 1 (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)) := le_max_right _ _
    have hxrdiv : (0 : ℝ) ≤ xr / lg ^ Bexp := by positivity
    calc BF ^ k * BG ^ k * (Real.sqrt (8 * Cdiv * 2 ^ e₁) * xr / lg ^ Bexp)
        = (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)) * (xr / lg ^ Bexp) := by ring
      _ ≤ max 1 (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)) * (xr / lg ^ Bexp) :=
          mul_le_mul_of_nonneg_right hm hxrdiv
      _ = max 1 (BF ^ k * BG ^ k * Real.sqrt (8 * Cdiv * 2 ^ e₁)) * xr / lg ^ Bexp := by ring
  exact hfinal


end Commons.NumberTheory.MaynardSieve
