import Mathlib
import Submission.Commons.NumberTheory.PrimesInAP.psi_in_AP_smallModulus

open Finset Filter
open scoped BigOperators

namespace Commons.NumberTheory.PrimesInAP

/-! ## Warm-up: sums over an arithmetic progression

We introduce the von Mangoldt sum `psiAP` and the (prime) theta sum `thetaAP`
restricted to a residue class `a mod q`, together with their basic order
properties, and the fact that an increase of `thetaAP` forces a prime in the
corresponding interval.
-/

/-- The von Mangoldt sum over `n ≤ N` with `n % q = a % q`. -/
noncomputable def psiAPNat (q a N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % q = a % q), ArithmeticFunction.vonMangoldt n

/-- The von Mangoldt sum over the progression `a mod q` up to the real point `y`. -/
noncomputable def psiAP (q a : ℕ) (y : ℝ) : ℝ := psiAPNat q a ⌊y⌋₊

/-- The `θ`-sum over primes `p ≤ N` with `p % q = a % q`. -/
noncomputable def thetaAPNat (q a N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % q = a % q), Real.log (p : ℝ)

/-- The `θ`-sum over primes in the progression `a mod q` up to the real point `y`. -/
noncomputable def thetaAP (q a : ℕ) (y : ℝ) : ℝ := thetaAPNat q a ⌊y⌋₊

lemma psiAP_eq (q a : ℕ) (y : ℝ) :
    psiAP q a y = ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q),
      ArithmeticFunction.vonMangoldt n := rfl

lemma thetaAP_eq (q a : ℕ) (y : ℝ) :
    thetaAP q a y = ∑ p ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun p => Nat.Prime p ∧ p % q = a % q),
      Real.log (p : ℝ) := rfl

/-- `thetaAP` written with an indicator for primality. -/
lemma thetaAP_eq_sum_if (q a : ℕ) (y : ℝ) :
    thetaAP q a y = ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q),
      (if Nat.Prime n then Real.log (n : ℝ) else 0) := by
  rw [thetaAP_eq, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hp, hq⟩; exact ⟨⟨hmem, hq⟩, hp⟩
  · rintro ⟨⟨hmem, hq⟩, hp⟩; exact ⟨hmem, hp, hq⟩

/-- `thetaAP` is bounded by `psiAP`. -/
lemma thetaAP_le_psiAP (q a : ℕ) (y : ℝ) : thetaAP q a y ≤ psiAP q a y := by
  rw [thetaAP_eq_sum_if, psiAP_eq]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hp : Nat.Prime n
  · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · rw [if_neg hp]; exact ArithmeticFunction.vonMangoldt_nonneg

/-- `psiAP` is bounded by the full Chebyshev `ψ`. -/
lemma psiAP_le_psi (q a : ℕ) (y : ℝ) : psiAP q a y ≤ Chebyshev.psi y := by
  rw [psiAP_eq, Chebyshev.psi_eq_sum_Icc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  intro n hn
  rw [Finset.mem_filter] at hn
  rw [Finset.mem_Icc] at hn ⊢
  exact ⟨by omega, hn.1.2⟩

/-- `thetaAP` is bounded by the full Chebyshev `θ`. -/
lemma thetaAP_le_theta (q a : ℕ) (y : ℝ) : thetaAP q a y ≤ Chebyshev.theta y := by
  rw [thetaAP_eq, Chebyshev.theta_eq_sum_Icc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rw [Finset.mem_Icc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2.1⟩
  · rw [Finset.mem_filter] at hn
    exact Real.log_nonneg (by exact_mod_cast hn.2.one_lt.le)

/-- The difference `psiAP - thetaAP` is controlled by the Chebyshev difference
`ψ - θ`, hence by a constant multiple of `sqrt y`. -/
lemma psiAP_sub_thetaAP_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q a : ℕ) (y : ℝ), psiAP q a y - thetaAP q a y ≤ C * Real.sqrt y := by
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C₀ 0, le_max_right _ _, fun q a y => ?_⟩
  have hsub : (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q)
      ⊆ Finset.Icc 0 ⌊y⌋₊ := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    exact ⟨by omega, hn.1.2⟩
  have hfnn : ∀ n ∈ Finset.Icc 0 ⌊y⌋₊,
      0 ≤ ArithmeticFunction.vonMangoldt n -
        (if Nat.Prime n then Real.log (n : ℝ) else 0) := by
    intro n _
    by_cases hp : Nat.Prime n
    · rw [if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, sub_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  have hSm : psiAP q a y - thetaAP q a y
      = ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q),
          (ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : ℝ) else 0)) := by
    rw [psiAP_eq, thetaAP_eq_sum_if, Finset.sum_sub_distrib]
  have hfull : Chebyshev.psi y - Chebyshev.theta y
      = ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : ℝ) else 0)) := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      Finset.sum_sub_distrib]
  rw [hSm]
  calc ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n % q = a % q),
          (ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : ℝ) else 0))
      ≤ ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : ℝ) else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hfnn n hn)
    _ = Chebyshev.psi y - Chebyshev.theta y := hfull.symm
    _ ≤ C₀ * Real.sqrt y := hC₀ y
    _ ≤ max C₀ 0 * Real.sqrt y := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg y)


/-- If the `thetaAPNat`-sum of a residue class strictly increases from `A` to `B`,
then there is a prime in the class in `(A, B]`. -/
lemma exists_prime_of_thetaAPNat_lt (q a : ℕ) {A B : ℕ}
    (h : thetaAPNat q a A < thetaAPNat q a B) :
    ∃ p : ℕ, Nat.Prime p ∧ p % q = a % q ∧ A < p ∧ p ≤ B := by
  by_contra hno
  have hsub : (Finset.Icc 1 B).filter (fun p => Nat.Prime p ∧ p % q = a % q)
      ⊆ (Finset.Icc 1 A).filter (fun p => Nat.Prime p ∧ p % q = a % q) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpIcc, hpp, hpm⟩ := hp
    rw [Finset.mem_Icc] at hpIcc ⊢
    refine ⟨⟨hpIcc.1, ?_⟩, hpp, hpm⟩
    by_contra hlt
    push_neg at hlt
    exact hno ⟨p, hpp, hpm, hlt, hpIcc.2⟩
  have hle : thetaAPNat q a B ≤ thetaAPNat q a A :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.1.1))
  linarith

/-- If `thetaAP` strictly increases across an interval, the interval contains a
prime in the progression. -/
lemma exists_prime_of_thetaAP_lt (q a : ℕ) {x y : ℝ}
    (h : thetaAP q a x < thetaAP q a y) :
    ∃ p : ℕ, Nat.Prime p ∧ p % q = a % q ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  obtain ⟨p, hpp, hpm, hAp, hpB⟩ :=
    exists_prime_of_thetaAPNat_lt q a (A := ⌊x⌋₊) (B := ⌊y⌋₊) (by simpa only [thetaAP] using h)
  refine ⟨p, hpp, hpm, ?_, ?_⟩
  · have h1 : ⌊x⌋₊ + 1 ≤ p := hAp
    calc x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
      _ ≤ (p : ℝ) := by exact_mod_cast h1
  · have hy0 : 0 ≤ y := by
      by_contra hy
      push_neg at hy
      have hz : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have : 2 ≤ p := hpp.two_le
      omega
    calc (p : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpB
      _ ≤ y := Nat.floor_le hy0

/-! ## Asymptotic helpers -/

/-- `(log x)^s · exp(-c (log x)^(1/4)) → 0`. -/
lemma tendsto_log_rpow_mul_exp_neg_quarter (s c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Real.log x) ^ s * Real.exp (-(c * (Real.log x) ^ (1/4 : ℝ))))
      atTop (nhds 0) := by
  have hφ : Tendsto (fun x : ℝ => (Real.log x) ^ (1/4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp Real.tendsto_log_atTop
  have hcomp : Tendsto
      (fun x : ℝ => ((Real.log x) ^ (1/4 : ℝ)) ^ (4 * s) *
        Real.exp (-c * (Real.log x) ^ (1/4 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 * s) c hc).comp hφ
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [← Real.rpow_mul hx0]
  rw [show (1/4 : ℝ) * (4 * s) = s by ring]
  rw [neg_mul]

/-- `(log x)^s / sqrt x → 0`. -/
lemma tendsto_log_rpow_div_sqrt (s : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ s / Real.sqrt x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ s / x ^ (1/2 : ℝ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (s := (1/2 : ℝ)) s (by norm_num)).tendsto_div_nhds_zero
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
  rw [Real.sqrt_eq_rpow]

/-- `K · (log x)^s / sqrt x ≤ 1` eventually. -/
lemma eventually_log_rpow_div_sqrt_le (s K : ℝ) (hK : 0 < K) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → K * ((Real.log x) ^ s / Real.sqrt x) ≤ 1 := by
  have ht : Tendsto (fun x : ℝ => K * ((Real.log x) ^ s / Real.sqrt x)) atTop (nhds 0) := by
    simpa using (tendsto_log_rpow_div_sqrt s).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.1 (ht.eventually_le_const (by norm_num : (0:ℝ) < 1))
  exact ⟨X, fun x hx => hX x hx⟩

/-- `log ((log x)^A + 2) ≤ sqrt (log x)` eventually. -/
lemma eventually_log_poly_add_two_le_sqrt {A : ℝ} (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, Real.log ((Real.log x) ^ A + 2) ≤ Real.sqrt (Real.log x) := by
  have hD : 0 < A + 1 := by linarith
  have hstep1 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ (1 / (A + 1)) * y ^ (1/2 : ℝ) := by
    have ht : Tendsto (fun y : ℝ => Real.log y / y ^ (1/2 : ℝ)) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
    have hle := ht.eventually_le_const (show (0:ℝ) < 1 / (A + 1) by positivity)
    filter_upwards [hle, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have hypos : 0 < y ^ (1/2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    rw [div_le_iff₀ hypos] at hy
    linarith [hy]
  have h2 : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) ≤ (1 / (A + 1)) * (Real.log x) ^ (1/2 : ℝ) :=
    Real.tendsto_log_atTop.eventually hstep1
  filter_upwards [h2, eventually_ge_atTop (Real.exp 3)] with x hx2 hx3
  have hlog3 : 3 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 3) hx3
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := by linarith
  have hLp1 : 1 ≤ (Real.log x) ^ A := Real.one_le_rpow (by linarith) hA.le
  have hLppos : 0 < (Real.log x) ^ A := lt_of_lt_of_le zero_lt_one hLp1
  have hstep : (Real.log x) ^ A + 2 ≤ (Real.log x) ^ (A + 1) := by
    rw [Real.rpow_add hlogpos, Real.rpow_one]
    nlinarith [hLp1, hLppos, hlog3]
  have hlog_le : Real.log ((Real.log x) ^ A + 2) ≤ Real.log ((Real.log x) ^ (A + 1)) :=
    Real.log_le_log (by positivity) hstep
  rw [Real.log_rpow hlogpos] at hlog_le
  have hfinal : (A + 1) * Real.log (Real.log x) ≤ (Real.log x) ^ (1/2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hx2 hD.le
    have hrw : (A + 1) * ((1 / (A + 1)) * (Real.log x) ^ (1/2 : ℝ))
        = (Real.log x) ^ (1/2 : ℝ) := by
      have h1 : (A + 1) * (1 / (A + 1)) = 1 := by
        rw [mul_one_div, div_self (ne_of_gt hD)]
      rw [← mul_assoc, h1, one_mul]
    rwa [hrw] at h
  rw [Real.sqrt_eq_rpow]
  exact le_trans hlog_le hfinal

/-- For every `A > 0`, `c > 0` and `K > 0`, uniformly over `q ≤ (log x)^A`,
`K (log x)^(2A) exp(-c sqrt(log x / log(q+2))) ≤ 1` eventually. -/
lemma eventually_log_pow_mul_exp_neg_le (A c K : ℝ) (hA : 0 < A) (hc : 0 < c) (hK : 0 < K) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, (q : ℝ) ≤ (Real.log x) ^ A →
      K * (Real.log x) ^ (2 * A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) ≤ 1 := by
  have htend : Tendsto (fun x : ℝ => K * ((Real.log x) ^ (2 * A) *
      Real.exp (-(c * (Real.log x) ^ (1/4 : ℝ))))) atTop (nhds 0) := by
    simpa using (tendsto_log_rpow_mul_exp_neg_quarter (2 * A) c hc).const_mul K
  have hev1 : ∀ᶠ x : ℝ in atTop,
      K * ((Real.log x) ^ (2 * A) * Real.exp (-(c * (Real.log x) ^ (1/4 : ℝ)))) ≤ 1 :=
    htend.eventually_le_const (by norm_num : (0:ℝ) < 1)
  have hcomb : ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ (Real.log x) ^ A →
      K * (Real.log x) ^ (2 * A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) ≤ 1 := by
    filter_upwards [hev1, eventually_log_poly_add_two_le_sqrt (A := A) hA,
      eventually_ge_atTop (Real.exp 1)] with x hx1 hx2 hx3
    intro q hqx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx3
    have hlog1 : 1 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 1) hx3
      rwa [Real.log_exp] at this
    have hlogpos : 0 < Real.log x := by linarith
    have hq2pos : 0 < (q : ℝ) + 2 := by positivity
    have hlogq2pos : 0 < Real.log ((q : ℝ) + 2) := by
      apply Real.log_pos
      have hq0 : (0:ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    have hle1 : Real.log ((q : ℝ) + 2) ≤ Real.log ((Real.log x) ^ A + 2) :=
      Real.log_le_log hq2pos (by linarith [hqx])
    have hleq : Real.log ((q : ℝ) + 2) ≤ Real.sqrt (Real.log x) := le_trans hle1 hx2
    have hdiv : Real.sqrt (Real.log x) ≤ Real.log x / Real.log ((q : ℝ) + 2) := by
      rw [le_div_iff₀ hlogq2pos]
      calc Real.sqrt (Real.log x) * Real.log ((q : ℝ) + 2)
          ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_left hleq (Real.sqrt_nonneg _)
        _ = Real.log x := Real.mul_self_sqrt (le_of_lt hlogpos)
    have hquarter : (Real.log x) ^ (1/4 : ℝ) ≤ Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)) := by
      have hss : Real.sqrt (Real.sqrt (Real.log x)) = (Real.log x) ^ (1/4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hlogpos)]
        norm_num
      rw [← hss]
      exact Real.sqrt_le_sqrt hdiv
    have hexp : Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
        ≤ Real.exp (-(c * (Real.log x) ^ (1/4 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hquarter hc.le
      linarith
    calc K * (Real.log x) ^ (2 * A) *
          Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
        ≤ K * (Real.log x) ^ (2 * A) * Real.exp (-(c * (Real.log x) ^ (1/4 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
      _ ≤ 1 := by
          rw [mul_assoc]
          exact hx1
  obtain ⟨X, hX⟩ := eventually_atTop.1 hcomb
  exact ⟨X, fun x hx => hX x hx⟩


/-- Arithmetic core of the short-interval argument: for large `x` and every
modulus `q ≤ (log x)^A`, the mass `x/(log x)^(2A)` dominates the two
Siegel--Walfisz error terms together with the prime-power correction. -/
lemma short_interval_AP_gain_pos (A c C Cb : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hC : 0 ≤ C) (hCb : 0 ≤ Cb) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ A →
      0 < x / (Real.log x) ^ (2 * A)
        - 2 * C * (x + x / (Real.log x) ^ A) *
            Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
        - Cb * Real.sqrt (x + x / (Real.log x) ^ A) := by
  obtain ⟨x₁, hx₁⟩ := eventually_log_pow_mul_exp_neg_le A c (16 * max C 1) hA hc
    (by positivity)
  obtain ⟨x₂, hx₂⟩ := eventually_log_rpow_div_sqrt_le (2 * A) (4 * Real.sqrt 2 * max Cb 1)
    (by positivity)
  refine ⟨max (max x₁ x₂) (Real.exp 1), ?_⟩
  intro x hx q hq1 hqx
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxexp : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxexp
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := by linarith
  have hLp1 : 1 ≤ (Real.log x) ^ A := Real.one_le_rpow hlog1 hA.le
  have hLppos : 0 < (Real.log x) ^ A := lt_of_lt_of_le zero_lt_one hLp1
  have hL2pos : 0 < (Real.log x) ^ (2 * A) := Real.rpow_pos_of_pos hlogpos _
  have hEpos : 0 < Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) :=
    Real.exp_pos _
  have hKpos : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKbpos : 0 < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- the two bounds
  have h1 : 2 * max C 1 * (1 + 1 / (Real.log x) ^ A) * (Real.log x) ^ (2 * A)
      * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) ≤ 1/4 := by
    have h16 := hx₁ x hxx₁ q hqx
    have hle : 1 + 1 / (Real.log x) ^ A ≤ 2 := by
      have := (div_le_one hLppos).mpr hLp1
      linarith
    have hfac : 0 ≤ 2 * max C 1 * (Real.log x) ^ (2 * A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by positivity
    calc 2 * max C 1 * (1 + 1 / (Real.log x) ^ A) * (Real.log x) ^ (2 * A)
          * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
        = (2 * max C 1 * (Real.log x) ^ (2 * A) *
            Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))))
          * (1 + 1 / (Real.log x) ^ A) := by ring
      _ ≤ (2 * max C 1 * (Real.log x) ^ (2 * A) *
            Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))) * 2 :=
          mul_le_mul_of_nonneg_left hle hfac
      _ = (1/4) * (16 * max C 1 * (Real.log x) ^ (2 * A) *
            Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))) := by ring
      _ ≤ (1/4) * 1 := by linarith [h16]
      _ = 1/4 := by norm_num
  have h2 : max Cb 1 * Real.sqrt 2 * ((Real.log x) ^ (2 * A) / Real.sqrt x) ≤ 1/4 := by
    have h4 := hx₂ x hxx₂
    nlinarith [h4]
  have hsum_eq : 2 * max C 1 * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      + max Cb 1 * Real.sqrt 2 * Real.sqrt x
      = (x / (Real.log x) ^ (2 * A)) *
        (2 * max C 1 * (1 + 1 / (Real.log x) ^ A) * (Real.log x) ^ (2 * A)
          * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
        + max Cb 1 * Real.sqrt 2 * ((Real.log x) ^ (2 * A) / Real.sqrt x)) := by
    have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
    have hsxne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
    have hL2ne : (Real.log x) ^ (2 * A) ≠ 0 := ne_of_gt hL2pos
    field_simp [hL2ne, hLppos.ne', hsxne, hx0.ne']
    ring_nf
    rw [hsx]
  have hkey : 2 * max C 1 * (1 + 1 / (Real.log x) ^ A) * (Real.log x) ^ (2 * A)
        * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      + max Cb 1 * Real.sqrt 2 * ((Real.log x) ^ (2 * A) / Real.sqrt x) < 1 := by
    linarith [h1, h2]
  have hfinalK : 2 * max C 1 * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      + max Cb 1 * Real.sqrt 2 * Real.sqrt x < x / (Real.log x) ^ (2 * A) := by
    rw [hsum_eq]
    calc (x / (Real.log x) ^ (2 * A)) *
          (2 * max C 1 * (1 + 1 / (Real.log x) ^ A) * (Real.log x) ^ (2 * A)
            * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
          + max Cb 1 * Real.sqrt 2 * ((Real.log x) ^ (2 * A) / Real.sqrt x))
        < (x / (Real.log x) ^ (2 * A)) * 1 :=
          mul_lt_mul_of_pos_left hkey (div_pos hx0 hL2pos)
      _ = x / (Real.log x) ^ (2 * A) := mul_one _
  have hxle : x + x / (Real.log x) ^ A ≤ 2 * x := by
    have : x / (Real.log x) ^ A ≤ x := (div_le_iff₀ hLppos).mpr (by nlinarith [hLp1, hx0])
    linarith
  have hterm1 : 2 * C * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      ≤ 2 * max C 1 * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by
    have ht : 0 ≤ 2 * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by positivity
    nlinarith [le_max_left C 1, ht]
  have hterm2 : Cb * Real.sqrt (x + x / (Real.log x) ^ A)
      ≤ max Cb 1 * Real.sqrt 2 * Real.sqrt x := by
    have hs : Real.sqrt (x + x / (Real.log x) ^ A) ≤ Real.sqrt (2 * x) :=
      Real.sqrt_le_sqrt hxle
    have h1 : Cb * Real.sqrt (x + x / (Real.log x) ^ A)
        ≤ max Cb 1 * Real.sqrt (x + x / (Real.log x) ^ A) :=
      mul_le_mul_of_nonneg_right (le_max_left Cb 1) (Real.sqrt_nonneg _)
    have h2 : max Cb 1 * Real.sqrt (x + x / (Real.log x) ^ A)
        ≤ max Cb 1 * Real.sqrt (2 * x) :=
      mul_le_mul_of_nonneg_left hs (le_of_lt hKbpos)
    rw [Real.sqrt_mul (show (0:ℝ) ≤ 2 by norm_num)] at h2
    linarith
  linarith [hterm1, hterm2, hfinalK]

/-- **Weak Goldbach**: primes in short intervals in arithmetic progressions. -/
theorem prime_in_short_interval_AP (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (q a : ℕ), 1 ≤ q →
      (q : ℝ) ≤ (Real.log x) ^ A → Nat.Coprime a q →
      ∃ p : ℕ, Nat.Prime p ∧ p % q = a % q ∧ x ≤ (p : ℝ) ∧
        (p : ℝ) ≤ x + x / (Real.log x) ^ A := by
  obtain ⟨c, C, hc, hC, X₁, hX₁⟩ := psi_in_AP_smallModulus A hA
  obtain ⟨Cb, hCb0, hCb⟩ := psiAP_sub_thetaAP_le_sqrt
  obtain ⟨X₂, hX₂⟩ := short_interval_AP_gain_pos A c C Cb hA hc hC.le hCb0
  refine ⟨max (max X₁ X₂) (Real.exp 1), ?_⟩
  intro x hx q a hq1 hqx hcop
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxexp : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxexp
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxexp
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log x := by linarith
  have hhpos : 0 < x / (Real.log x) ^ A := div_pos hx0 (Real.rpow_pos_of_pos hlogpos A)
  have hEpos : 0 < Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) :=
    Real.exp_pos _
  have hxha : x ≤ x + x / (Real.log x) ^ A := by linarith
  -- Siegel--Walfisz at `x`
  have hb1 := hX₁ x hxX₁ q a hq1 hqx hcop
  have hb1' : psiAP q a x - x / (Nat.totient q : ℝ) ≤
      C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by
    simpa only [← psiAP_eq] using (abs_le.mp hb1).2
  -- Siegel--Walfisz at `x + x/(log x)^A`
  have hqxa : (q : ℝ) ≤ (Real.log (x + x / (Real.log x) ^ A)) ^ A := by
    have hlogle : Real.log x ≤ Real.log (x + x / (Real.log x) ^ A) := Real.log_le_log hx0 hxha
    calc (q : ℝ) ≤ (Real.log x) ^ A := hqx
      _ ≤ (Real.log (x + x / (Real.log x) ^ A)) ^ A := Real.rpow_le_rpow hlogpos.le hlogle hA.le
  have hb2 := hX₁ (x + x / (Real.log x) ^ A) (le_trans hxX₁ hxha) q a hq1 hqxa hcop
  have hlogq2pos : 0 < Real.log ((q : ℝ) + 2) := by
    apply Real.log_pos
    have hq0 : (0:ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hmono : Real.exp (-(c * Real.sqrt (Real.log (x + x / (Real.log x) ^ A) /
        Real.log ((q : ℝ) + 2))))
      ≤ Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by
    apply Real.exp_le_exp.mpr
    have h1 : Real.log x / Real.log ((q : ℝ) + 2)
        ≤ Real.log (x + x / (Real.log x) ^ A) / Real.log ((q : ℝ) + 2) :=
      div_le_div_of_nonneg_right (Real.log_le_log hx0 hxha) hlogq2pos.le
    have h2 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hc.le
    linarith
  have hcineq : C * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log (x + x / (Real.log x) ^ A) /
          Real.log ((q : ℝ) + 2))))
      ≤ C * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have hb2' : -(C * (x + x / (Real.log x) ^ A) *
        Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))))
      ≤ psiAP q a (x + x / (Real.log x) ^ A)
        - (x + x / (Real.log x) ^ A) / (Nat.totient q : ℝ) := by
    have h := (abs_le.mp hb2).1
    rw [← psiAP_eq] at h
    linarith
  have hR1 : psiAP q a (x + x / (Real.log x) ^ A) - thetaAP q a (x + x / (Real.log x) ^ A)
      ≤ Cb * Real.sqrt (x + x / (Real.log x) ^ A) := hCb q a _
  have hR2 : 0 ≤ psiAP q a x - thetaAP q a x := by
    have := thetaAP_le_psiAP q a x; linarith
  have hgain := hX₂ x hxX₂ q hq1 hqx
  have hphi_le : x / (Real.log x) ^ (2 * A)
      ≤ (x / (Real.log x) ^ A) / (Nat.totient q : ℝ) := by
    have hphipos : 0 < (Nat.totient q : ℝ) := by
      have := Nat.totient_pos.mpr (by omega : 0 < q)
      exact_mod_cast this
    have hphile : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq1
    have h1 : (x / (Real.log x) ^ A) / (q : ℝ)
        ≤ (x / (Real.log x) ^ A) / (Nat.totient q : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hphipos hphile
    have h2 : x / (Real.log x) ^ (2 * A) ≤ (x / (Real.log x) ^ A) / (q : ℝ) := by
      have h4 : (x / (Real.log x) ^ A) / (Real.log x) ^ A = x / (Real.log x) ^ (2 * A) := by
        rw [div_div, ← Real.rpow_add hlogpos, show A + A = 2 * A by ring]
      rw [← h4]
      exact div_le_div_of_nonneg_left (by positivity) hqpos hqx
    linarith
  have hident : thetaAP q a (x + x / (Real.log x) ^ A) - thetaAP q a x
      = (psiAP q a (x + x / (Real.log x) ^ A) - psiAP q a x)
        - (psiAP q a (x + x / (Real.log x) ^ A) - thetaAP q a (x + x / (Real.log x) ^ A))
        + (psiAP q a x - thetaAP q a x) := by ring
  have hCE : 0 ≤ C * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) :=
    mul_nonneg hC.le hEpos.le
  have hcx : C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      ≤ C * (x + x / (Real.log x) ^ A) *
          Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2)))) := by
    have h := mul_nonneg hCE hhpos.le
    nlinarith [h, hxha]
  have hpsid : (x + x / (Real.log x) ^ A) / (Nat.totient q : ℝ) - x / (Nat.totient q : ℝ)
      - C * (x + x / (Real.log x) ^ A) *
          Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      - C * x * Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      ≤ psiAP q a (x + x / (Real.log x) ^ A) - psiAP q a x := by
    linarith [hb2', hb1']
  have hpsid2 : (x / (Real.log x) ^ A) / (Nat.totient q : ℝ)
      - 2 * C * (x + x / (Real.log x) ^ A) *
          Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      ≤ psiAP q a (x + x / (Real.log x) ^ A) - psiAP q a x := by
    have hsplit : (x + x / (Real.log x) ^ A) / (Nat.totient q : ℝ) - x / (Nat.totient q : ℝ)
        = (x / (Real.log x) ^ A) / (Nat.totient q : ℝ) := by
      rw [← sub_div]; ring
    linarith [hpsid, hcx, hsplit]
  have htheta_lb : (x / (Real.log x) ^ A) / (Nat.totient q : ℝ)
      - 2 * C * (x + x / (Real.log x) ^ A) *
          Real.exp (-(c * Real.sqrt (Real.log x / Real.log ((q : ℝ) + 2))))
      - Cb * Real.sqrt (x + x / (Real.log x) ^ A)
      ≤ thetaAP q a (x + x / (Real.log x) ^ A) - thetaAP q a x := by
    rw [hident]
    linarith [hpsid2, hR1, hR2]
  have hlt : thetaAP q a x < thetaAP q a (x + x / (Real.log x) ^ A) := by
    rw [← sub_pos]
    linarith [htheta_lb, hgain, hphi_le]
  obtain ⟨p, hpp, hpm, hxp, hpb⟩ := exists_prime_of_thetaAP_lt q a hlt
  exact ⟨p, hpp, hpm, le_of_lt hxp, hpb⟩

end Commons.NumberTheory.PrimesInAP
