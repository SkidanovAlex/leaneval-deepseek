import Mathlib
import Submission.Work.FIArea7.PolarCoeff6
import Submission.Work.FIArea6.beta_sq_mass_tight

/-!
# `Work.FIArea6.vsq_polar` — the squared mass of `β_z` for the structural polar class

`β` is assumed only to be `Work.FIArea7.IsPolarCoeff` for `Pa` and `φ` — support in the polar
box (5.14) with (5.8)/(5.9), `|z|²` squarefree on the support, and the pointwise bound
`‖β z‖ ≤ τ(|z|²)`.  All the estimates of `Work.FIArea6.beta_sq_mass_tight` use `IsBetaCoeff`
only through exactly that structural content (via `beta_support`, `beta_norm_le_divisors`,
`tau_le_two_pow`, `card_support_le` and the Möbius squarefreeness of the support), so the whole
proof transcribes verbatim with the five substitutions recorded in
`Submission/Work/FIArea6/PolarCoeff.lean`.  The restructured case split drops the sub-case
`θ < N^{-1/6}/10^6` (handled in `beta_sq_mass_nonfat`): the `loglog x > 20` sub-cases
`lattice_case`/`crude_case` are valid unconditionally there, and the `loglog x ≤ 20` sub-case
(`T² ≤ θ^{-1}`) is valid throughout the fat sector `θ√N ≥ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open Work.FIArea6
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The structural accessors of `IsPolarCoeff` -/

/-- The support triple of an `IsPolarCoeff`: polar box, freedom of small primes, `τ`-bound. -/
private lemma polar_support {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FIArea7.IsPolarCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) :=
  ⟨hβ.inPolarBox hz, hβ.noSmallPrimes hz, hβ.tau_le hz⟩

/-! ## Parameter helpers, `lattice_case` and `crude_case` (verbatim, with the polar accessors) -/

private lemma exp_two_lt : Real.exp 2 < 7.4 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

private lemma exp_four_lt : Real.exp 4 < 54.8 := by
  have h : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_two_lt, Real.exp_pos 2]

private lemma exp_eight_lt : Real.exp 8 < 3005 := by
  have h : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_four_lt, Real.exp_pos 4]

private lemma exp_sixteen_lt : Real.exp 16 < 9.1e6 := by
  have h : Real.exp 16 = Real.exp 8 * Real.exp 8 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_eight_lt, Real.exp_pos 8]

private lemma exp_twenty_lt : Real.exp 20 < 5e8 := by
  have h : Real.exp 20 = Real.exp 16 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_sixteen_lt, exp_four_lt, Real.exp_pos 16, Real.exp_pos 4]

private lemma exp_twelve_lt : Real.exp 12 < 1.7e5 := by
  have h : Real.exp 12 = Real.exp 8 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_eight_lt, exp_four_lt, Real.exp_pos 8, Real.exp_pos 4]

private lemma exp_three_lt : Real.exp 3 < 20.2 := by
  have h : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_two_lt, Real.exp_one_lt_d9, Real.exp_pos 2, Real.exp_pos 1]

private lemma exp_two_gt : (7.385 : ℝ) < Real.exp 2 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]

private lemma exp_four_gt : (54.5 : ℝ) < Real.exp 4 := by
  have h : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_two_gt, Real.exp_pos 2]

private lemma exp_eight_gt : (2970 : ℝ) < Real.exp 8 := by
  have h : Real.exp 8 = Real.exp 4 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_four_gt, Real.exp_pos 4]

private lemma exp_sixteen_gt : (8.82e6 : ℝ) < Real.exp 16 := by
  have h : Real.exp 16 = Real.exp 8 * Real.exp 8 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_eight_gt, Real.exp_pos 8]

private lemma exp_twenty_gt : (4e8 : ℝ) < Real.exp 20 := by
  have h : Real.exp 20 = Real.exp 16 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h]; nlinarith [exp_sixteen_gt, exp_four_gt, Real.exp_pos 16, Real.exp_pos 4]

private lemma exp_le_cube {u : ℝ} (h0 : 0.08 ≤ u) (h1 : u ≤ 20) :
    Real.exp u ≤ 756000 * u ^ 3 := by
  by_cases h1' : u ≤ 3
  · have he : Real.exp u ≤ Real.exp 3 := Real.exp_le_exp.mpr h1'
    have hc : (0.08:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith [he, exp_three_lt, hc]
  · have h1'' : 3 < u := not_le.mp h1'
    by_cases h2 : u ≤ 4
    · have he : Real.exp u ≤ Real.exp 4 := Real.exp_le_exp.mpr h2
      have hc : (3:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
      nlinarith [he, exp_four_lt, hc]
    · have h2' : 4 < u := not_le.mp h2
      by_cases h3 : u ≤ 8
      · have he : Real.exp u ≤ Real.exp 8 := Real.exp_le_exp.mpr h3
        have hc : (4:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        nlinarith [he, exp_eight_lt, hc]
      · have h3' : 8 < u := not_le.mp h3
        by_cases h4 : u ≤ 12
        · have he : Real.exp u ≤ Real.exp 12 := Real.exp_le_exp.mpr h4
          have hc : (8:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
          nlinarith [he, exp_twelve_lt, hc]
        · have h4' : 12 < u := not_le.mp h4
          by_cases h5 : u ≤ 16
          · have he : Real.exp u ≤ Real.exp 16 := Real.exp_le_exp.mpr h5
            have hc : (12:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
            nlinarith [he, exp_sixteen_lt, hc]
          · have h5' : 16 < u := not_le.mp h5
            have he : Real.exp u ≤ Real.exp 20 := Real.exp_le_exp.mpr h1
            have hc : (16:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
            nlinarith [he, exp_twenty_lt, hc]

private lemma exp_ge_twenty_mul (u : ℝ) :
    Real.exp u ≥ Real.exp 20 * (u - 19) := by
  have h : Real.exp u = Real.exp 20 * Real.exp (u - 20) := by
    rw [← Real.exp_add]; ring_nf
  rw [h]
  have h1 : (u - 20) + 1 ≤ Real.exp (u - 20) := Real.add_one_le_exp _
  nlinarith [Real.exp_pos 20]


/-- **The pointwise cap is small when `loglog x ≤ 20`.** -/
private lemma T_sq_le_inv_theta (Pa : Work.FITop.Params)
    (hu : Real.log (Real.log (Pa.x : ℝ)) ≤ 20) :
    ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ))) ^ 2 ≤ 1 / Pa.θ := by
  set u : ℝ := Real.log (Real.log (Pa.x : ℝ)) with hudef
  have hu08 : 0.08 ≤ u := loglogx_ge Pa
  have hu_pos : 0 < u := lt_of_lt_of_le (by norm_num) hu08
  have hx1 : (1:ℝ) < (Pa.x : ℝ) := by
    have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx1 : 0 < Real.log (Pa.x : ℝ) := Real.log_pos hx1
  have hexpu : Real.exp u = Real.log (Pa.x : ℝ) := Real.exp_log hlogx1
  have hlogPz_ge : u^2 ≤ Real.log (Pa.Pz : ℝ) := Pa.hPlo
  have hlogPz_pos : 0 < Real.log (Pa.Pz : ℝ) := lt_of_lt_of_le (by positivity) hlogPz_ge
  have h2Npos : (0:ℝ) < 2 * Pa.N := by
    have h : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    linarith
  have hNsq : Pa.N ≤ Real.sqrt (Pa.x : ℝ) := N_le_sqrt_x Pa
  have hlog2N : Real.log (2 * Pa.N) ≤ Real.log 2 + (1/2) * Real.exp u := by
    have h1 : Real.log (2 * Pa.N) ≤ Real.log (2 * Real.sqrt (Pa.x : ℝ)) := by
      apply Real.log_le_log (by linarith)
      linarith
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ((Real.sqrt_pos.mpr (by linarith : (0:ℝ) < (Pa.x:ℝ))).ne'), Real.log_sqrt (le_of_lt (by linarith : (0:ℝ) < (Pa.x:ℝ)))] at h1
    rw [hexpu]
    linarith
  have hkey : 2 * Real.log 2 * (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)) ≤ (2:ℝ)^20 * u := by
    have hdiv : Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)
        ≤ (Real.log 2 + (1/2) * Real.exp u) / u^2 := by
      apply div_le_div₀ (by positivity) hlog2N (by positivity) hlogPz_ge
    have hlog2lt : Real.log 2 ≤ 0.6932 := le_trans (le_of_lt Real.log_two_lt_d9) (by norm_num)
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hcube : Real.exp u ≤ 756000 * u^3 := exp_le_cube hu08 hu
    have hA : 2 * Real.log 2 * Real.log 2 / u^2 ≤ (2:ℝ)^19 * u := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 2 * Real.log 2 * Real.log 2 ≤ 1 := by nlinarith
      have h2 : (1:ℝ) ≤ (2:ℝ)^19 * u^3 := by
        have h3 : (0.08:ℝ)^3 ≤ u^3 := pow_le_pow_left₀ (by norm_num) hu08 3
        nlinarith
      nlinarith
    have hB : Real.log 2 * Real.exp u / u^2 ≤ (2:ℝ)^19 * u := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : Real.log 2 * Real.exp u ≤ 0.6932 * (756000 * u^3) :=
        mul_le_mul hlog2lt hcube (le_of_lt (Real.exp_pos u)) (by norm_num)
      nlinarith [h1, sq_nonneg u]
    have hsplit : 2 * Real.log 2 * ((Real.log 2 + (1/2) * Real.exp u) / u^2)
        = 2 * Real.log 2 * Real.log 2 / u^2 + Real.log 2 * Real.exp u / u^2 := by
      field_simp
    have hml := mul_le_mul_of_nonneg_left hdiv (by linarith : (0:ℝ) ≤ 2 * Real.log 2)
    calc 2 * Real.log 2 * (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ))
        ≤ 2 * Real.log 2 * ((Real.log 2 + (1/2) * Real.exp u) / u^2) := hml
      _ = 2 * Real.log 2 * Real.log 2 / u^2 + Real.log 2 * Real.exp u / u^2 := hsplit
      _ ≤ (2:ℝ)^19 * u + (2:ℝ)^19 * u := add_le_add hA hB
      _ = (2:ℝ)^20 * u := by ring
  have hA'u : (2:ℝ)^20 * u ≤ Pa.A' * u := by
    have h : (2:ℝ)^20 ≤ Pa.A' := by
      have h2 : (2:ℝ)^(20:ℕ) ≤ Pa.A' := exp_two_pow_le_A' Pa
      simpa using h2
    exact mul_le_mul_of_nonneg_right h (le_of_lt hu_pos)
  have hT2 : ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ))) ^ 2
      = Real.exp (2 * Real.log 2 * (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul]
    ring_nf
  have honetheta : 1 / Pa.θ = Real.exp (Pa.A' * u) := by
    rw [Pa.hθ, Real.rpow_neg (le_of_lt hlogx1), one_div, inv_inv]
    rw [Real.rpow_def_of_pos hlogx1]
    congr 1
    ring
  rw [hT2, honetheta]
  apply Real.exp_le_exp.mpr
  linarith [hkey, hA'u]

private lemma card_divisors_eq_two_pow_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [Nat.card_divisors hn0]
  have h1 : ∀ p ∈ n.primeFactors, n.factorization p + 1 = 2 := by
    intro p hp
    have hle : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn0).mp hn p
    have hge : 1 ≤ n.factorization p := by
      have h2 : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have h3 : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact (h3.dvd_iff_one_le_factorization hn0).mp h2
    omega
  rw [Finset.prod_congr rfl (fun p hp => h1 p hp), Finset.prod_const]

/-- `∏_{p ∣ d}(2p-1) ≤ 2^{ω(d)}·d`. -/
private lemma prod_two_mul_sub_one_le {d : ℕ} (hd0 : d ≠ 0) :
    (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ)) ≤ (2:ℝ) ^ d.primeFactors.card * d := by
  have h1 : (∏ p ∈ d.primeFactors, (2 * p - 1 : ℕ)) ≤ 2 ^ d.primeFactors.card * d := by
    calc ∏ p ∈ d.primeFactors, (2 * p - 1 : ℕ) ≤ ∏ p ∈ d.primeFactors, (2 * p) := by
          apply Finset.prod_le_prod₀
          · intro p hp
            have := Nat.prime_of_mem_primeFactors hp
            omega
          · intro p hp; omega
      _ = 2 ^ d.primeFactors.card * (∏ p ∈ d.primeFactors, p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 2 ^ d.primeFactors.card * d := by
          apply Nat.mul_le_mul_left
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Nat.prod_primeFactors_dvd d)
  calc (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
      = ((∏ p ∈ d.primeFactors, (2 * p - 1 : ℕ) : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ((2 ^ d.primeFactors.card * d : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2:ℝ) ^ d.primeFactors.card * d := by push_cast; ring

/-- `d·(10θ√N/d + 1)² = 100θ²N/d + 20θ√N + d`. -/
private lemma key_arith {θ N d : ℝ} (hd : 0 < d) (hN : 0 ≤ N) :
    d * (10 * θ * Real.sqrt N / d + 1)^2
      = 100 * θ^2 * N / d + 20 * θ * Real.sqrt N + d := by
  have h : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have hsq : (10 * θ * Real.sqrt N / d + 1)^2
      = 100 * θ^2 * (Real.sqrt N)^2 / d^2 + 2 * (10 * θ * Real.sqrt N / d) + 1 := by ring
  rw [hsq, h]
  field_simp
  ring
private lemma lattice_case (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea7.IsPolarCoeff Pa φ β)
    (hu20 : 20 < Real.log (Real.log (Pa.x : ℝ)))
    (hθ1 : Pa.θ ≤ 1) (hN1 : (1:ℝ) ≤ Pa.N)
    (hA' : Pa.A' * Real.log (Real.log (Pa.x : ℝ))
      ≤ Real.log (Pa.N) / 3 - 4000 * (1 + Real.log (Real.log (Pa.N : ℝ)))) :
    (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2)
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
  classical
  obtain ⟨Cloc, hClocpos, hClocle, hCloc⟩ := Work.FIArea6.tau_small_divisor_localization
  set s : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hsdef
  have hsum : ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := sum_support Pa β
  have hx1 : (1:ℝ) < (Pa.x : ℝ) := by
    have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx1 : 0 < Real.log (Pa.x : ℝ) := Real.log_pos hx1
  have hNpos : (0:ℝ) < (Pa.N : ℝ) := by linarith
  -- **`N` is enormous**: `log N > 10^8`
  have hlogN_ge : (1e8:ℝ) < Real.log (Pa.N : ℝ) := by
    have h1 : (Pa.x:ℝ) ^ ((1:ℝ)/4 + Pa.η) < (Pa.N : ℝ) := Pa.hNlo
    have h2 : Real.log ((Pa.x:ℝ) ^ ((1:ℝ)/4 + Pa.η)) < Real.log (Pa.N : ℝ) :=
      Real.log_lt_log (Real.rpow_pos_of_pos (by positivity) _) h1
    rw [Real.log_rpow (by positivity)] at h2
    have h3 : (1:ℝ)/4 * Real.log (Pa.x:ℝ) ≤ ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x:ℝ) := by
      nlinarith [le_of_lt hlogx1, le_of_lt Pa.hη]
    have h4 : Real.log (Pa.x:ℝ) = Real.exp (Real.log (Real.log (Pa.x:ℝ))) :=
      (Real.exp_log hlogx1).symm
    have h5 : Real.exp 20 < Real.exp (Real.log (Real.log (Pa.x:ℝ))) := Real.exp_lt_exp.mpr hu20
    linarith [h2, h3, h4, h5, exp_twenty_gt]
  have hN4 : (4:ℝ) ≤ Pa.N := by
    have h2 : Real.log 4 ≤ Real.log (Pa.N:ℝ) := by
      rw [Real.log_four_eq]
      have := Real.log_two_lt_d9
      linarith
    have h3 := (Real.le_log_iff_exp_le hNpos).mp h2
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 4)] at h3
  -- **the support**: `n = |z|²` is positive, squarefree, and `≤ 2N`
  have hn0 : ∀ z ∈ s, Work.FIPlan.gnorm z ≠ 0 := by
    intro z hz h0
    have hb := (polar_support hβ (Finset.mem_filter.mp hz).2).1
    have hb2 := hb.2.1
    rw [h0] at hb2
    simp at hb2
    linarith [Pa.hN1]
  have hsqfree : ∀ z ∈ s, Squarefree (Work.FIPlan.gnorm z) := by
    intro z hz
    exact hβ.squarefree (Finset.mem_filter.mp hz).2
  have hnle : ∀ z ∈ s, (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
    intro z hz
    have hb := (polar_support hβ (Finset.mem_filter.mp hz).2).1
    have h2 := hb.2.2.1
    nlinarith [h2, hθ1, hN1]
  -- **pointwise**: `‖β z‖² ≤ 4^{ω(n)}`
  have hpt : ∀ z ∈ s, ‖β z‖ ^ 2 ≤ (4:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card := by
    intro z hz
    have h1 : ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
      hβ.2 z
    have h0a : (0:ℝ) ≤ ‖β z‖ := norm_nonneg _
    have h0b : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        ≤ (2:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card := by
      rw [card_divisors_eq_two_pow_of_squarefree (hn0 z hz) (hsqfree z hz)]
      exact le_of_eq (by push_cast; ring)
    have h0c : (0:ℝ) ≤ (2:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card := by positivity
    have h3 : ((2:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card) ^ 2
        = (4:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card := by
      rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have h4 : ‖β z‖ ^ 2 ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2 := by
      nlinarith [h1, h0a, h0b, sq_nonneg (‖β z‖ - (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))]
    have h5 : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
        ≤ ((2:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card)^2 := by
      nlinarith [h2, h0b, h0c,
        sq_nonneg ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) - (2:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card)]
    rw [h3] at h5
    linarith [h4, h5]
  -- the divisor index set `Dsq`
  set Y : ℕ := max 2 ⌈(((2 * Pa.N : ℝ)) ^ (1/3 : ℝ))⌉₊ with hYdef
  have hY2 : 2 ≤ Y := le_max_left _ _
  have hYceil : ∀ d ∈ (Finset.Icc 1 Y).filter (fun d => Squarefree d), d ≤ Y :=
    fun d hd => (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  have hYbound : (Y:ℝ) ≤ 2 * (((2 * Pa.N : ℝ)) ^ (1/3:ℝ)) + 2 := by
    have h1 : ((⌈(((2 * Pa.N : ℝ)) ^ (1/3 : ℝ))⌉₊ : ℕ) : ℝ)
        ≤ (((2 * Pa.N : ℝ)) ^ (1/3:ℝ)) + 1 := by
      have h := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ ((2 * Pa.N : ℝ)) ^ (1/3:ℝ))
      linarith
    have h2 : ((2:ℕ) : ℝ) ≤ 2 * (((2 * Pa.N : ℝ)) ^ (1/3:ℝ)) + 2 := by
      have h := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 2 * Pa.N) (1/3:ℝ)
      linarith
    have h3 : ((max 2 ⌈(((2 * Pa.N : ℝ)) ^ (1/3 : ℝ))⌉₊ : ℕ) : ℝ)
        = max ((2:ℕ) : ℝ) (((⌈(((2 * Pa.N : ℝ)) ^ (1/3 : ℝ))⌉₊ : ℕ)) : ℝ) :=
      Nat.cast_max 2 _
    rw [hYdef, h3]
    exact max_le h2 (by linarith)
  set Dsq : Finset ℕ := (Finset.Icc 1 Y).filter (fun d => Squarefree d) with hDdef
  have hYle : ∀ d ∈ Dsq, d ≤ Y := hYceil
  have hDsq : ∀ d ∈ Dsq, Squarefree d := fun d hd => (Finset.mem_filter.mp hd).2
  have hDpos : ∀ d ∈ Dsq, 1 ≤ d := fun d hd => (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  -- every divisor `d ∣ n` with `d³ ≤ n` lies in `Dsq`
  have hdiv : ∀ z ∈ s, (Work.FIPlan.gnorm z).divisors.filter
      (fun d => d^3 ≤ Work.FIPlan.gnorm z) ⊆ Dsq := by
    intro z hz d hdmem
    obtain ⟨hddvd, hd3⟩ := Finset.mem_filter.mp hdmem
    have hdvd : d ∣ Work.FIPlan.gnorm z := Nat.dvd_of_mem_divisors hddvd
    rw [hDdef, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hddvd).ne', ?_⟩, ?_⟩
    · have h1 : (d:ℝ)^3 ≤ 2 * Pa.N := by
        have h2 : ((d^3 : ℕ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast hd3
        push_cast at h2
        linarith [hnle z hz]
      have h2 : (d:ℝ) = ((d:ℝ)^3)^(1/3:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have h3 : (d:ℝ) ≤ (((2 * Pa.N : ℝ)) ^ (1/3 : ℝ)) := by
        have hdpos : (0:ℝ) < (d:ℝ) := by
          have hp := Nat.pos_of_mem_divisors hddvd
          exact_mod_cast hp
        rw [h2]
        exact Real.rpow_le_rpow (le_of_lt (pow_pos hdpos 3)) h1 (by norm_num)
      have h4 : (d:ℝ) ≤ (Y:ℝ) := by
        have h5 : (d:ℝ) ≤ ((⌈(((2 * Pa.N : ℝ)) ^ (1/3 : ℝ))⌉₊ : ℕ) : ℝ) :=
          le_trans h3 (Nat.le_ceil _)
        exact le_trans h5 (by rw [hYdef]; exact_mod_cast le_max_right 2 _)
      exact_mod_cast h4
    · exact Squarefree.squarefree_of_dvd hdvd (hsqfree z hz)
  -- **exchange the sums**
  have hswap : (∑ z ∈ s, ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
        (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6)
      ≤ ∑ d ∈ Dsq, (((d.divisors.card : ℕ)) : ℝ)^6
          * ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
    have h1 : ∀ z ∈ s, (∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
          (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6)
        ≤ ∑ d ∈ Dsq, (if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ)) : ℝ)^6 else 0) := by
      intro z hz
      have hcongr : (∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
            (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6)
          = ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter (fun d => d^3 ≤ Work.FIPlan.gnorm z),
              (if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ)) : ℝ)^6 else 0) := by
        apply Finset.sum_congr rfl
        intro d hdmem
        rw [if_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdmem).1)]
      rw [hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg (hdiv z hz)
        (fun d hd hds => by positivity)
    calc (∑ z ∈ s, ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
            (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6)
        ≤ ∑ z ∈ s, ∑ d ∈ Dsq,
            (if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ)) : ℝ)^6 else 0) :=
          Finset.sum_le_sum h1
      _ = ∑ d ∈ Dsq, ∑ z ∈ s,
            (if d ∣ Work.FIPlan.gnorm z then (((d.divisors.card : ℕ)) : ℝ)^6 else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ Dsq, (((d.divisors.card : ℕ)) : ℝ)^6
            * ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hcard : (((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℕ) : ℝ)
              = ∑ z ∈ s, (if d ∣ Work.FIPlan.gnorm z then (1:ℝ) else 0) := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hcard, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases h : d ∣ Work.FIPlan.gnorm z
          · rw [if_pos h, if_pos h]; ring
          · rw [if_neg h, if_neg h]; ring
  -- **the count**
  have hcount : ∀ d ∈ Dsq, ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
          * (10 * Pa.θ * Real.sqrt Pa.N / (d : ℝ) + 1) ^ 2 := by
    intro d hd
    refine Work.FIArea6.card_polarBox_dvd_le Pa φ d ?_ (hDsq d hd)
      (s.filter (fun z => d ∣ Work.FIPlan.gnorm z)) ?_
    · have h1 : 1 ≤ d := hDpos d hd
      omega
    · intro z hz
      rw [Finset.mem_filter] at hz
      exact ⟨(polar_support hβ (Finset.mem_filter.mp hz.1).2).1, hz.2⟩
  have hθnn : (0:ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
  have hsNnn : (0:ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hYnnN : (0:ℝ) ≤ (Y:ℝ) := by positivity
  -- **the weighted bound for each `d`**
  have hw : ∀ d ∈ Dsq, (((d.divisors.card : ℕ)) : ℝ)^6
        * ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ (2:ℝ) ^ (7 * d.primeFactors.card)
          * (100 * Pa.θ ^ 2 * Pa.N / (d:ℝ) + 20 * Pa.θ * Real.sqrt Pa.N + d) := by
    intro d hd
    have hd0 : d ≠ 0 := by have h1 := hDpos d hd; omega
    have hd0R : (0:ℝ) < (d:ℝ) := by
      have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hDpos d hd
      linarith
    have h1 : (((d.divisors.card : ℕ)) : ℝ)^6 = (2:ℝ) ^ (6 * d.primeFactors.card) := by
      rw [card_divisors_eq_two_pow_of_squarefree hd0 (hDsq d hd)]
      push_cast
      rw [← pow_mul]
      ring_nf
    have h2 : (∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
        ≤ (2:ℝ) ^ d.primeFactors.card * d := prod_two_mul_sub_one_le hd0
    have h3 : (2:ℝ) ^ (6 * d.primeFactors.card) * (2:ℝ) ^ d.primeFactors.card
        = (2:ℝ) ^ (7 * d.primeFactors.card) := by
      rw [← pow_add]
      ring_nf
    have h4 := key_arith (θ := Pa.θ) (N := Pa.N) (d := (d:ℝ)) hd0R (by linarith)
    calc (((d.divisors.card : ℕ)) : ℝ)^6
          * ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
        ≤ (2:ℝ) ^ (6 * d.primeFactors.card)
          * ((∏ p ∈ d.primeFactors, ((2 * p - 1 : ℕ) : ℝ))
              * (10 * Pa.θ * Real.sqrt Pa.N / (d:ℝ) + 1)^2) := by
          rw [h1]
          exact mul_le_mul_of_nonneg_left (hcount d hd) (by positivity)
      _ ≤ (2:ℝ) ^ (6 * d.primeFactors.card)
          * (((2:ℝ) ^ d.primeFactors.card * d)
              * (10 * Pa.θ * Real.sqrt Pa.N / (d:ℝ) + 1)^2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((2:ℝ) ^ (6 * d.primeFactors.card) * (2:ℝ) ^ d.primeFactors.card)
          * ((d:ℝ) * (10 * Pa.θ * Real.sqrt Pa.N / (d:ℝ) + 1)^2) := by ring
      _ = (2:ℝ) ^ (7 * d.primeFactors.card)
          * ((d:ℝ) * (10 * Pa.θ * Real.sqrt Pa.N / (d:ℝ) + 1)^2) := by
          rw [h3]
      _ = (2:ℝ) ^ (7 * d.primeFactors.card)
          * (100 * Pa.θ ^ 2 * Pa.N / (d:ℝ) + 20 * Pa.θ * Real.sqrt Pa.N + d) := by
          rw [h4]
  -- **the weighted sums**
  set W : ℝ := ∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card) / (d:ℝ) with hWdef
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    positivity
  have hWs : (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card)) ≤ (Y:ℝ) * W := by
    rw [hWdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hDpos d hd
      linarith
    have hle : (d:ℝ) ≤ Y := by exact_mod_cast hYle d hd
    have hp : (0:ℝ) < (2:ℝ) ^ (7 * d.primeFactors.card) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hd0]
    nlinarith [hle, hp]
  have hWl : (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card) * d) ≤ (Y:ℝ)^2 * W := by
    rw [hWdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hDpos d hd
      linarith
    have hle : (d:ℝ) ≤ Y := by exact_mod_cast hYle d hd
    have hYnn : (0:ℝ) ≤ Y := by positivity
    have hp : (0:ℝ) < (2:ℝ) ^ (7 * d.primeFactors.card) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hd0]
    have hdd : (d:ℝ) * (d:ℝ) ≤ Y * Y := by nlinarith [hle, hd0, hYnn]
    nlinarith [hdd, hp, hd0]
  have hWsum : ∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card)
        * (100 * Pa.θ ^ 2 * Pa.N / (d:ℝ) + 20 * Pa.θ * Real.sqrt Pa.N + d)
      ≤ (100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2) * W := by
    have hsplit : ∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card)
          * (100 * Pa.θ ^ 2 * Pa.N / (d:ℝ) + 20 * Pa.θ * Real.sqrt Pa.N + d)
        = 100 * Pa.θ ^ 2 * Pa.N * W
          + 20 * Pa.θ * Real.sqrt Pa.N * (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card))
          + (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card) * d) := by
      rw [hWdef, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rw [hsplit]
    have h2 := mul_le_mul_of_nonneg_left hWs
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 20) hθnn) hsNnn)
    calc 100 * Pa.θ ^ 2 * Pa.N * W
          + 20 * Pa.θ * Real.sqrt Pa.N * (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card))
          + (∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card) * d)
        ≤ 100 * Pa.θ ^ 2 * Pa.N * W
          + 20 * Pa.θ * Real.sqrt Pa.N * ((Y:ℝ) * W) + (Y:ℝ)^2 * W := by
          exact add_le_add (add_le_add (le_refl _) h2) hWl
      _ = (100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2) * W := by ring
  -- **putting it together**
  calc ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := hsum
    _ ≤ ∑ z ∈ s, Cloc * ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
          (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6 := by
        apply Finset.sum_le_sum
        intro z hz
        have hloc : (4:ℝ) ^ (Work.FIPlan.gnorm z).primeFactors.card
            ≤ Cloc * ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
                (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6 :=
          hCloc (Work.FIPlan.gnorm z) (Nat.one_le_iff_ne_zero.mpr (hn0 z hz)) (hsqfree z hz)
        exact le_trans (hpt z hz) hloc
    _ = Cloc * ∑ z ∈ s, ∑ d ∈ (Work.FIPlan.gnorm z).divisors.filter
          (fun d => d^3 ≤ Work.FIPlan.gnorm z), (((d.divisors.card : ℕ)) : ℝ)^6 := by
        rw [Finset.mul_sum]
    _ ≤ Cloc * ∑ d ∈ Dsq, (((d.divisors.card : ℕ)) : ℝ)^6
          * ((s.filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hswap (le_of_lt hClocpos)
    _ ≤ Cloc * ∑ d ∈ Dsq, (2:ℝ) ^ (7 * d.primeFactors.card)
          * (100 * Pa.θ ^ 2 * Pa.N / (d:ℝ) + 20 * Pa.θ * Real.sqrt Pa.N + d) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_of_lt hClocpos)
    _ ≤ Cloc * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2) * W) :=
        mul_le_mul_of_nonneg_left hWsum (le_of_lt hClocpos)
    _ ≤ Cloc * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
          * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)))) := by
        have hθnn : (0:ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
        have hsNnn : (0:ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
        have hYnn : (0:ℝ) ≤ (Y:ℝ) := by positivity
        have hpos1 : (0:ℝ) ≤ 100 * Pa.θ^2 * Pa.N :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt (by linarith))
        have hpos2 : (0:ℝ) ≤ 20 * Pa.θ * Real.sqrt Pa.N * Y :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθnn) hsNnn) hYnn
        have hpos3 : (0:ℝ) ≤ (Y:ℝ)^2 := sq_nonneg _
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hClocpos)
        exact mul_le_mul_of_nonneg_left (Work.FIArea6.weighted_tau_sum_le Y hY2 Dsq hYle) (by linarith [hpos1, hpos2, hpos3])
    _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
        have hlogY1 : (0:ℝ) ≤ Real.log Y + 1 := by
          have h1 : (1:ℝ) ≤ (Y:ℝ) := by
            have h2 : (2:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY2
            linarith
          exact add_nonneg (Real.log_nonneg h1) (by norm_num)
        have hX : 0 ≤ (100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
            * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1))) := by
          apply mul_nonneg
          · have hN0 : (0:ℝ) ≤ Pa.N := by linarith
            have h1 : (0:ℝ) ≤ 100 * Pa.θ ^ 2 * Pa.N :=
              mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hN0
            have h2 : (0:ℝ) ≤ 20 * Pa.θ * Real.sqrt Pa.N * Y :=
              mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθnn) hsNnn) hYnnN
            have h3 : (0:ℝ) ≤ (Y:ℝ)^2 := sq_nonneg _
            linarith
          · exact mul_nonneg hlogY1 (le_of_lt (Real.exp_pos _))
        have hstep : Cloc * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
              * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1))))
            ≤ 100 * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
              * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)))) :=
          mul_le_mul_of_nonneg_right hClocle hX
        have hfin := Work.FIArea6.lattice_numeric_final Pa Y hY2 hYbound hu20 hlogN_ge hN1 Pa.hθ0 hA'
        calc Cloc * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
              * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1))))
            ≤ 100 * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
              * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1)))) := hstep
          _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
              have h100 : (100:ℝ) * ((100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
                    * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1))))
                  = 100 * (100 * Pa.θ ^ 2 * Pa.N + 20 * Pa.θ * Real.sqrt Pa.N * Y + Y^2)
                    * ((Real.log Y + 1) * Real.exp (4000 * (Real.log (Real.log Y) + 1))) := by ring
              rw [h100]
              exact hfin

private lemma logN_ge_of_hu20 (Pa : Work.FITop.Params)
    (hu20 : 20 < Real.log (Real.log (Pa.x : ℝ))) :
    (1e8:ℝ) < Real.log (Pa.N : ℝ) := by
  have hx1 : (1:ℝ) < (Pa.x : ℝ) := by
    have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx1 : 0 < Real.log (Pa.x : ℝ) := Real.log_pos hx1
  have h1 : (Pa.x:ℝ) ^ ((1:ℝ)/4 + Pa.η) < (Pa.N : ℝ) := Pa.hNlo
  have h2 : Real.log ((Pa.x:ℝ) ^ ((1:ℝ)/4 + Pa.η)) < Real.log (Pa.N : ℝ) :=
    Real.log_lt_log (Real.rpow_pos_of_pos (by positivity) _) h1
  rw [Real.log_rpow (by positivity)] at h2
  have h3 : (1:ℝ)/4 * Real.log (Pa.x:ℝ) ≤ ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x:ℝ) := by
    nlinarith [le_of_lt hlogx1, le_of_lt Pa.hη]
  have h4 : Real.log (Pa.x:ℝ) = Real.exp (Real.log (Real.log (Pa.x:ℝ))) :=
    (Real.exp_log hlogx1).symm
  have h5 : Real.exp 20 < Real.exp (Real.log (Real.log (Pa.x:ℝ))) := Real.exp_lt_exp.mpr hu20
  linarith [h2, h3, h4, h5, exp_twenty_gt]
private lemma crude_case (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea7.IsPolarCoeff Pa φ β)
    (h1 : Pa.θ * ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)))^2
        ≤ 1.67 * (Real.log (2 + Pa.N))^3)
    (h2 : ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)))^2
        ≤ 1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N))^3) :
    (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2)
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
  classical
  set s : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hsdef
  have hsum : ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := sum_support Pa β
  set T : ℝ := (2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)) with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  have hθ1' : Pa.θ ≤ 1 := theta_le_one_of_params Pa
  have hθnn : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hsNnn : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hN1r : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN1' : (0:ℝ) < Pa.N := by linarith
  have hlogPz_pos : 0 < Real.log (Pa.Pz : ℝ) := by
    have h := loglogx_ge Pa
    have h2 := Pa.hPlo
    nlinarith
  -- the pointwise `T`-bound
  have hptT : ∀ z ∈ s, ‖β z‖ ^ 2 ≤ T ^ 2 := by
    intro z hz
    have hz' : β z ≠ 0 := (Finset.mem_filter.mp hz).2
    have h1' : ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
      hβ.2 z
    have ht := IsPolarCoeff.tau_le_two_pow hβ hz'
    have hgn_pos : (0:ℝ) < (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
      have hb := (polar_support hβ hz').1
      have hN := hb.2.1
      linarith [hN1']
    have hgn_le : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) ≤ 2 * Pa.N := by
      have hb := (polar_support hβ hz').1
      have h2' := hb.2.2.1
      nlinarith [h2', hθ1', hN1r]
    have hle : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ T := by
      refine le_trans ht ?_
      rw [hTdef]
      refine (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr ?_
      exact div_le_div_of_nonneg_right (Real.log_le_log hgn_pos hgn_le) (le_of_lt hlogPz_pos)
    have h0 : (0:ℝ) ≤ ‖β z‖ := norm_nonneg _
    have h3 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h1', hle, h0, h3, hTnn]
  -- the pointwise `τ`-bound
  have hptτ : ∀ z ∈ s, ‖β z‖ ^ 2 ≤ Pa.τ ^ 2 := by
    intro z hz
    have hz' : β z ≠ 0 := (Finset.mem_filter.mp hz).2
    have h1' : ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
      hβ.2 z
    have h4 : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ :=
      (polar_support hβ hz').2.2
    have h0 : (0:ℝ) ≤ ‖β z‖ := norm_nonneg _
    have h3 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hτ0 : 0 ≤ Pa.τ := le_trans (Real.rpow_nonneg (by linarith [logx_ge Pa]) _) Pa.hτ1
    have h4' : ‖β z‖ ≤ Pa.τ := le_trans h1' h4
    have h5' : ‖β z‖ ^ 2 ≤ Pa.τ ^ 2 := by
      nlinarith [h4', h0, hτ0, sq_nonneg (‖β z‖ - Pa.τ)]
    exact h5'
  have hτsq : Pa.τ ^ 2 ≤ Real.sqrt Pa.N := by
    have hτ4 : Pa.τ ≤ Pa.N ^ (1/4 : ℝ) := tau_le_quarter Pa
    have hτ0 : 0 ≤ Pa.τ := le_trans (Real.rpow_nonneg (by linarith [logx_ge Pa]) _) Pa.hτ1
    have h2' : (Pa.N ^ (1/4:ℝ)) ^ (2:ℕ) = Pa.N ^ (1/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN1'.le]
      norm_num
    calc Pa.τ ^ 2 ≤ (Pa.N ^ (1/4:ℝ)) ^ (2:ℕ) := by nlinarith [hτ4, hτ0]
      _ = Pa.N ^ (1/2 : ℝ) := h2'
      _ = Real.sqrt Pa.N := by rw [Real.sqrt_eq_rpow]
  have hcard := IsPolarCoeff.card_support_le Pa φ β hβ
  have hlog1 : (1:ℝ) ≤ (Real.log (2 + Pa.N)) ^ 3 := by
    have h3 : (3:ℝ) ≤ 2 + Pa.N := by linarith
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3
    have h4 : (1:ℝ) < Real.log 3 := by
      have hh := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at hh
    exact one_le_pow₀ (le_of_lt (lt_of_lt_of_le h4 h))
  have hmin : min (T^2) (Pa.τ^2) ≤ T^2 := min_le_left _ _
  have hmin2 : min (T^2) (Pa.τ^2) ≤ Pa.τ^2 := min_le_right _ _
  have hT2b : T ^ 2 ≤ 1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
    rw [hTdef]; exact h2
  have h1b : Pa.θ * T ^ 2 ≤ 1.67 * (Real.log (2 + Pa.N)) ^ 3 := by
    rw [hTdef]; exact h1
  calc ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := hsum
    _ ≤ ∑ z ∈ s, min (T^2) (Pa.τ^2) := by
        apply Finset.sum_le_sum
        intro z hz
        exact le_min (hptT z hz) (hptτ z hz)
    _ = (s.card : ℝ) * min (T^2) (Pa.τ^2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * min (T^2) (Pa.τ^2) := by
        have h0 : 0 ≤ min (T^2) (Pa.τ^2) := le_min (sq_nonneg T) (sq_nonneg Pa.τ)
        nlinarith [hcard, h0]
    _ ≤ 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3
          + 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3
          + 334 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
        have hA : 200 * (Pa.θ ^ 2 * Pa.N) * min (T^2) (Pa.τ^2)
            ≤ 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
          calc 200 * (Pa.θ ^ 2 * Pa.N) * min (T^2) (Pa.τ^2)
              ≤ 200 * (Pa.θ ^ 2 * Pa.N) * T^2 :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ = 200 * (Pa.θ * Pa.N) * (Pa.θ * T^2) := by ring
            _ ≤ 200 * (Pa.θ * Pa.N) * (1.67 * (Real.log (2 + Pa.N)) ^ 3) :=
                mul_le_mul_of_nonneg_left h1b (mul_nonneg (by norm_num) (mul_nonneg hθnn hN1'.le))
            _ = 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by ring
        have hB : 200 * (Pa.θ * Real.sqrt Pa.N) * min (T^2) (Pa.τ^2)
            ≤ 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
          calc 200 * (Pa.θ * Real.sqrt Pa.N) * min (T^2) (Pa.τ^2)
              ≤ 200 * (Pa.θ * Real.sqrt Pa.N) * T^2 :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ ≤ 200 * (Pa.θ * Real.sqrt Pa.N) * (1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3) :=
                mul_le_mul_of_nonneg_left hT2b (by positivity)
            _ = 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
                have hsq : Real.sqrt Pa.N * Real.sqrt Pa.N = Pa.N := Real.mul_self_sqrt hN1'.le
                calc 200 * (Pa.θ * Real.sqrt Pa.N) * (1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3)
                    = 334 * Pa.θ * (Real.sqrt Pa.N * Real.sqrt Pa.N) * (Real.log (2 + Pa.N)) ^ 3 := by ring
                  _ = 334 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by rw [hsq]
        have hC : 200 * min (T^2) (Pa.τ^2) ≤ 334 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
          calc 200 * min (T^2) (Pa.τ^2) ≤ 200 * Pa.τ^2 :=
                mul_le_mul_of_nonneg_left hmin2 (by norm_num)
            _ ≤ 200 * Real.sqrt Pa.N := mul_le_mul_of_nonneg_left hτsq (by norm_num)
            _ ≤ 334 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
                nlinarith [hlog1, hsNnn]
        have hexp : 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * min (T^2) (Pa.τ^2)
            = 200 * (Pa.θ ^ 2 * Pa.N) * min (T^2) (Pa.τ^2)
              + 200 * (Pa.θ * Real.sqrt Pa.N) * min (T^2) (Pa.τ^2)
              + 200 * min (T^2) (Pa.τ^2) := by ring
        rw [hexp]
        linarith [hA, hB, hC]
    _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
        have hp : (0:ℝ) ≤ (Real.log (2 + Pa.N)) ^ 3 := by positivity
        have h0 : 0 ≤ Pa.θ * Pa.N := mul_nonneg hθnn hN1'.le
        nlinarith [hlog1, h0, hsNnn, hp]
/-! ## The main estimate -/

theorem vsq_polar6 (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea7.IsPolarCoeff Pa φ β) :
    ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
  set s : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) with hs
  have hsum : ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 :=
    sum_support Pa β
  have hcard : (s.card : ℝ)
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) :=
    IsPolarCoeff.card_support_le Pa φ β hβ
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_of_params Pa
  have hθ0 : 0 ≤ Pa.θ := Pa.hθ0.le
  have hlog1 : 1 ≤ Real.log (2 + Pa.N) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact le_of_lt (lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) (by linarith)))
  have hpt : ∀ z ∈ s, ‖β z‖ ^ 2 ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2 := by
    intro z hz
    have hz' : β z ≠ 0 := (Finset.mem_filter.mp hz).2
    have h := hβ.2 z
    have h0 : 0 ≤ ‖β z‖ := norm_nonneg _
    have h1 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h, h0, h1]
  have hττ : ∀ z ∈ s, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2
      ≤ Pa.τ ^ 2 := by
    intro z hz
    have hz' : β z ≠ 0 := (Finset.mem_filter.mp hz).2
    have h := (polar_support hβ hz').2.2
    have h0 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hτ0 : 0 ≤ Pa.τ := le_trans (Real.rpow_nonneg (by linarith [logx_ge Pa]) _) Pa.hτ1
    nlinarith [h, h0, hτ0]
  have hcrude : ∑ z ∈ s, ‖β z‖ ^ 2
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.τ ^ 2 := by
    calc ∑ z ∈ s, ‖β z‖ ^ 2 ≤ ∑ z ∈ s, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum hpt
      _ ≤ ∑ _z ∈ s, Pa.τ ^ 2 := Finset.sum_le_sum hττ
      _ = (s.card : ℝ) * Pa.τ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.τ ^ 2 := by
          have h0 : 0 ≤ Pa.τ ^ 2 := sq_nonneg _
          nlinarith [hcard, h0]
  have hτ4 : Pa.τ ≤ Pa.N ^ (1/4 : ℝ) := tau_le_quarter Pa
  have hτsq : Pa.τ ^ 2 ≤ Real.sqrt Pa.N := by
    have hN0 : (0:ℝ) ≤ Pa.N := by linarith
    have hτ0 : 0 ≤ Pa.τ := le_trans (Real.rpow_nonneg (by linarith [logx_ge Pa]) _) Pa.hτ1
    have h2 : (Pa.N ^ (1/4:ℝ)) ^ (2:ℕ) = Pa.N ^ (1/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
      norm_num
    calc Pa.τ ^ 2 ≤ (Pa.N ^ (1/4:ℝ)) ^ (2:ℕ) := by nlinarith [hτ4, hτ0]
      _ = Pa.N ^ (1/2 : ℝ) := h2
      _ = Real.sqrt Pa.N := by rw [Real.sqrt_eq_rpow]
  by_cases hA : Pa.θ * Real.sqrt Pa.N ≤ 1
  · -- small sector
    have hsN : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
    have hθ2N : Pa.θ ^ 2 * Pa.N = (Pa.θ * Real.sqrt Pa.N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ Pa.N)]
    have hcount : 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) ≤ 600 := by
      have h1 : Pa.θ ^ 2 * Pa.N ≤ 1 := by
        rw [hθ2N]
        have h0 : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg hθ0 hsN
        nlinarith [hA, h0]
      have h2 : Pa.θ * Real.sqrt Pa.N ≤ 1 := hA
      linarith
    calc ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := hsum
      _ ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) * Pa.τ ^ 2 := hcrude
      _ ≤ 600 * Real.sqrt Pa.N := by
          have h0 : 0 ≤ Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1 := by positivity
          nlinarith [hcount, hτsq, h0, sq_nonneg Pa.τ]
      _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
          have hlog3 : (1:ℝ) ≤ (Real.log (2 + Pa.N)) ^ 3 := one_le_pow₀ hlog1
          have hpos : 0 ≤ Pa.θ * Pa.N := mul_nonneg hθ0 (by linarith)
          have hb : 0 ≤ Real.sqrt Pa.N := hsN
          have h1 : (600:ℝ) * Real.sqrt Pa.N
              ≤ 600 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) := by nlinarith
          have h2 : (600:ℝ) * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1)
              ≤ 600 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
            nlinarith [hlog3, hpos, hb]
          have h3 : (600:ℝ) * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3
              ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
            nlinarith [hlog3, hpos, hb]
          linarith
  · -- fat sector `θ√N ≥ 1`
    rw [not_le] at hA
    by_cases hu20 : Real.log (Real.log (Pa.x : ℝ)) ≤ 20
    · -- `loglog x ≤ 20`: the pointwise `NoSmallPrimes` cap on `τ(|z|²)` is at most `θ^{-1/2}`,
      -- so the crude bound `#support · T²` closes the estimate.
      have hu08 : 0.08 ≤ Real.log (Real.log (Pa.x : ℝ)) := loglogx_ge Pa
      have hlogPz_pos : 0 < Real.log (Pa.Pz : ℝ) := by
        have h := Pa.hPlo
        nlinarith
      set T : ℝ := (2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)) with hTdef
      have hTnn : 0 ≤ T := by rw [hTdef]; positivity
      have hT2 : T ^ 2 ≤ 1 / Pa.θ := T_sq_le_inv_theta Pa hu20
      have hpoint : ∀ z ∈ s, ‖β z‖ ^ 2 ≤ T ^ 2 := by
        intro z hz
        have hz' : β z ≠ 0 := (Finset.mem_filter.mp hz).2
        have h1 : ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := hβ.2 z
        have ht := IsPolarCoeff.tau_le_two_pow hβ hz'
        have hgn_pos : (0:ℝ) < (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
          have hb := (polar_support hβ hz').1
          have hN := hb.2.1
          linarith [hN1]
        have hgn_le : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) ≤ 2 * Pa.N := by
          have hb := (polar_support hβ hz').1
          have h2 := hb.2.2.1
          nlinarith [h2, hθ1, hN1]
        have hle : (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ T := by
          refine le_trans ht ?_
          rw [hTdef]
          refine (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr ?_
          exact div_le_div_of_nonneg_right (Real.log_le_log hgn_pos hgn_le) (le_of_lt hlogPz_pos)
        nlinarith [h1, hle, norm_nonneg (β z), hTnn]
      have hcard2 : (s.card : ℝ) ≤ 600 * Pa.θ ^ 2 * Pa.N := by
        have hs1 : 1 ≤ Pa.θ * Real.sqrt Pa.N := le_of_lt hA
        have hsq : Real.sqrt Pa.N ^ 2 = Pa.N := Real.sq_sqrt (by linarith)
        have hsqn : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
        nlinarith [hcard, hs1, hsq, hsqn, Pa.hθ0]
      calc ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 = ∑ z ∈ s, ‖β z‖ ^ 2 := hsum
        _ ≤ ∑ _z ∈ s, T ^ 2 := Finset.sum_le_sum hpoint
        _ = (s.card : ℝ) * T ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 600 * Pa.θ ^ 2 * Pa.N * (1 / Pa.θ) := by
            nlinarith [hcard2, hT2, sq_nonneg T]
        _ = 600 * Pa.θ * Pa.N := by
            field_simp
        _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := by
            have h3 : (1:ℝ) ≤ (Real.log (2 + Pa.N)) ^ 3 := one_le_pow₀ hlog1
            have h0 : (0:ℝ) ≤ Pa.θ * Pa.N := mul_nonneg hθ0 (by linarith)
            have hb : (0:ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
            nlinarith [h3, h0, hb]
    · -- `loglog x > 20`: either the divisor-sum argument (localisation + lattice count) or
      -- the crude pointwise bound closes the estimate.
      have hu20' : 20 < Real.log (Real.log (Pa.x : ℝ)) := lt_of_not_ge hu20
      by_cases hAb : Pa.A' * Real.log (Real.log (Pa.x : ℝ))
          ≤ Real.log (Pa.N) / 3 - 4000 * (1 + Real.log (Real.log (Pa.N : ℝ)))
      · exact lattice_case Pa φ β hβ hu20' hθ1 (by linarith) hAb
      · obtain ⟨hc1, hc2⟩ := Work.FIArea6.crude_arith Pa hu20'
          (logN_ge_of_hu20 Pa hu20') (by linarith) (lt_of_not_ge hAb)
        exact crude_case Pa φ β hβ hc1 hc2

end

end Work.FIArea7
