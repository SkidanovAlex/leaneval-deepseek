import Mathlib
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv

/-!
# `∑_{q ≤ Q} 1/φ(q) ≪ (log Q)²`

We prove that there is a constant `C > 0` such that for every `Q ≥ 2`,

$\sum_{q=1}^{Q} \frac{1}{\varphi(q)} \le C\,(\log Q)^2 .$

**Strategy.**  By Euler's product formula, for `q ≥ 2`

$\frac{q}{\varphi(q)} = \prod_{p \mid q}\frac{p}{p-1}
  \le \prod_{p \le q}\frac{p}{p-1}.$

The second Mertens theorem (`sum_log_prime_ratio_real_tendsto` in the shared
commons) gives `Σ_{p≤x} log(p/(p-1)) − log log x → γ`, hence
`∏_{p≤x} p/(p-1) ≤ A·log x` eventually; monotonicity of the partial product
makes this global: `∏_{p≤q} p/(p-1) ≤ C·log q` for every real `q ≥ 2`.

Consequently `1/φ(q) ≤ C·log q / q`, and summing (with the harmonic bound
`Σ_{q≤Q} 1/q ≤ 1 + log Q`) yields `Σ_{q≤Q} 1/φ(q) ≤ 1 + C·log Q·(1 + log Q)`,
which is `O((log Q)²)` since `log Q ≥ log 2 > 0`.
-/

open scoped BigOperators
open Filter

namespace Commons.NumberTheory.Totient

noncomputable section

/-- `∏_{p ≤ x} p/(p-1)` (with the workspace convention `p ≤ x` for reals). -/
private def prodPrimeRatio (x : ℝ) : ℝ :=
  ∏ p ∈ (⌊x⌋₊).primesLE, ((p : ℝ) / ((p : ℝ) - 1))

/-- `Σ_{p ≤ x} log(p/(p-1))`. -/
private def logPrimeRatioSum (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- Each factor `p/(p-1)` is positive. -/
private lemma primeRatio_pos (p : ℕ) (hp : 2 ≤ p) :
    0 < (p : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : 0 < (p : ℝ) := by
    have hpR : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hp)
    linarith
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  exact div_pos hp0 hp1

/-- Each factor `p/(p-1)` is at least `1`. -/
private lemma primeRatio_one_le (p : ℕ) (hp : 2 ≤ p) :
    1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : 0 < (p : ℝ) - 1 := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [le_div_iff₀ hp1]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  linarith

/-- `log(∏_{p ≤ x} p/(p-1)) = Σ_{p ≤ x} log(p/(p-1))`. -/
private lemma log_prodPrimeRatio_eq_sum {x : ℝ} (_hx : 2 ≤ x) :
    Real.log (prodPrimeRatio x) = logPrimeRatioSum x := by
  unfold prodPrimeRatio logPrimeRatioSum
  refine Real.log_prod ?_
  intro p hp
  have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
  exact ne_of_gt (primeRatio_pos p hp2)

/-- `∏_{p ≤ x} p/(p-1) = exp(Σ_{p ≤ x} log(p/(p-1)))`. -/
private lemma prodPrimeRatio_eq_exp_sum {x : ℝ} (hx : 2 ≤ x) :
    prodPrimeRatio x = Real.exp (logPrimeRatioSum x) := by
  have hpos : 0 < prodPrimeRatio x := by
    unfold prodPrimeRatio
    refine Finset.prod_pos ?_
    intro p hp
    exact primeRatio_pos p (Nat.mem_primesLE.mp hp).2.two_le
  calc prodPrimeRatio x = Real.exp (Real.log (prodPrimeRatio x)) := (Real.exp_log hpos).symm
    _ = Real.exp (logPrimeRatioSum x) := by rw [log_prodPrimeRatio_eq_sum hx]

/-- The partial product is monotone in the real variable. -/
private lemma prodPrimeRatio_mono {x y : ℝ} (hxy : x ≤ y) :
    prodPrimeRatio x ≤ prodPrimeRatio y := by
  have hf : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  unfold prodPrimeRatio
  refine Finset.prod_le_prod_of_subset_of_one_le₀ ?h ?hf0 ?hf1
  · intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨le_trans (Nat.mem_primesLE.mp hp).1 hf, (Nat.mem_primesLE.mp hp).2⟩
  · intro p hp
    exact le_of_lt (primeRatio_pos p (Nat.mem_primesLE.mp hp).2.two_le)
  · intro p hp _hpnot
    exact primeRatio_one_le p (Nat.mem_primesLE.mp hp).2.two_le

/-- Second Mertens theorem in product form: `∏_{p ≤ x} p/(p-1) ≤ A·log x`
eventually (for `x ≥ X₀`, where `X₀ ≥ 3`). -/
private lemma prodPrimeRatio_eventually_le_mul_log :
    ∃ (A : ℝ) (_hA : 0 < A) (X₀ : ℝ), 3 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x → prodPrimeRatio x ≤ A * Real.log x := by
  let γ := Real.eulerMascheroniConstant
  have hT : Tendsto (fun x : ℝ => logPrimeRatioSum x - Real.log (Real.log x))
      atTop (nhds γ) := by
    simpa [logPrimeRatioSum] using (Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto :
      Tendsto (fun x : ℝ =>
        (∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))) -
          Real.log (Real.log x)) atTop (nhds γ))
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hT) (1 : ℝ) zero_lt_one
  let X₀ : ℝ := max N 3
  let A : ℝ := Real.exp (γ + 1)
  refine ⟨A, Real.exp_pos _, X₀, ?_, ?_⟩
  · dsimp [X₀]
    exact le_max_right N 3
  · intro x hx
    have hxN : N ≤ x := le_trans (le_max_left N 3) hx
    have hsub : logPrimeRatioSum x - Real.log (Real.log x) ≤ γ + 1 := by
      have hlt := hN x hxN
      have hring : (logPrimeRatioSum x - Real.log (Real.log x)) - γ =
          logPrimeRatioSum x - (γ + Real.log (Real.log x)) := by ring
      have habs : |(logPrimeRatioSum x - Real.log (Real.log x)) - γ| < 1 := by
        simpa [Real.dist_eq, hring] using hlt
      have h1 : (logPrimeRatioSum x - Real.log (Real.log x)) - γ ≤ 1 := by
        calc (logPrimeRatioSum x - Real.log (Real.log x)) - γ
            ≤ |(logPrimeRatioSum x - Real.log (Real.log x)) - γ| := le_abs_self _
        _ ≤ 1 := le_of_lt habs
      linarith
    have hmain : logPrimeRatioSum x ≤ γ + 1 + Real.log (Real.log x) := by linarith
    have hlogpos : 0 < Real.log x := by
      have hx3 : 3 ≤ x := le_trans (le_max_right N 3) hx
      exact Real.log_pos (by linarith : (1 : ℝ) < x)
    calc
      prodPrimeRatio x = Real.exp (logPrimeRatioSum x) := prodPrimeRatio_eq_exp_sum (by
        have hx3 : 3 ≤ x := le_trans (le_max_right N 3) hx
        linarith)
      _ ≤ Real.exp (γ + 1 + Real.log (Real.log x)) := Real.exp_le_exp.mpr hmain
      _ = Real.exp (γ + 1) * Real.log x := by
        rw [Real.exp_add, Real.exp_log hlogpos]
      _ = A * Real.log x := by rfl

/-- **Global product bound:** there is `C > 0` with
`∏_{p ≤ x} p/(p-1) ≤ C·log x` for every real `x ≥ 2`. -/
private lemma prodPrimeRatio_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → prodPrimeRatio x ≤ C * Real.log x := by
  obtain ⟨A, hApos, X₀, hX03, hEv⟩ := prodPrimeRatio_eventually_le_mul_log
  refine ⟨A * (Real.log X₀ / Real.log 2), ?pos, ?main⟩
  · have hlogX₀ : 0 < Real.log X₀ := Real.log_pos (by have h3 : (3 : ℝ) ≤ X₀ := hX03; linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_pos hApos (div_pos hlogX₀ hlog2)
  · intro x hx2
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx2 : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ x)
    have hlogX₀ : 0 < Real.log X₀ :=
      Real.log_pos (by have h3 : (3 : ℝ) ≤ X₀ := hX03; linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_cases hxX : X₀ ≤ x
    · have hpx : prodPrimeRatio x ≤ A * Real.log x := hEv x hxX
      have hCgeA : A ≤ A * (Real.log X₀ / Real.log 2) := by
        have h2leX : (2 : ℝ) ≤ X₀ := by linarith
        have hle : Real.log 2 ≤ Real.log X₀ :=
          Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2leX
        have hratio : (1 : ℝ) ≤ Real.log X₀ / Real.log 2 := (one_le_div hlog2).2 hle
        simpa using (mul_le_mul_of_nonneg_left hratio (le_of_lt hApos))
      have hfin : A * Real.log x ≤ (A * (Real.log X₀ / Real.log 2)) * Real.log x := by
        exact mul_le_mul_of_nonneg_right hCgeA (le_of_lt hlogxpos)
      exact le_trans hpx hfin
    · have hxX' : x ≤ X₀ := le_of_not_ge hxX
      have hpx : prodPrimeRatio x ≤ prodPrimeRatio X₀ := prodPrimeRatio_mono hxX'
      have hPX : prodPrimeRatio X₀ ≤ A * Real.log X₀ := hEv X₀ (le_rfl)
      have hfin : A * Real.log X₀ ≤ (A * (Real.log X₀ / Real.log 2)) * Real.log x := by
        have hCglog2 : A * (Real.log X₀ / Real.log 2) * Real.log 2 = A * Real.log X₀ := by
          field_simp [ne_of_gt hlog2]
        calc
          A * Real.log X₀ = A * (Real.log X₀ / Real.log 2) * Real.log 2 := hCglog2.symm
          _ ≤ A * (Real.log X₀ / Real.log 2) * Real.log x := by
            exact mul_le_mul_of_nonneg_left hlogx2
              (mul_nonneg (le_of_lt hApos) (le_of_lt (div_pos hlogX₀ hlog2)))
      exact le_trans (le_trans hpx hPX) hfin

/-! ## From the product bound to `1/φ(q) ≤ C·log q / q` -/

/-- Euler's product formula for `φ(n)/n` over the reals:
for `n ≠ 0`, `φ(n)/n = ∏_{p | n} (1 − 1/p)`. -/
theorem totient_ratio_real (n : ℕ) (hn : n ≠ 0) :
    ((Nat.totient n : ℝ) / (n : ℝ)) =
      ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hq := totient_ratio_eq_prod_one_sub_inv n hn
  have hqR := congrArg (fun q : ℚ => (q : ℝ)) hq
  simpa using hqR

/-- Reciprocal Euler product: for `n ≠ 0`,
`n/φ(n) = ∏_{p | n} p/(p-1)`. -/
private lemma totient_div_totient_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hφpos : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 := totient_ratio_real n hn
  have h1inv : (Nat.totient n : ℝ)⁻¹ * (n : ℝ) =
      (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := by
    calc
      (Nat.totient n : ℝ)⁻¹ * (n : ℝ) = ((Nat.totient n : ℝ) / (n : ℝ))⁻¹ := by
        field_simp [hnR]
      _ = (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := by rw [h1]
  calc
    (n : ℝ) / (Nat.totient n : ℝ) = (n : ℝ) * (Nat.totient n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ = (Nat.totient n : ℝ)⁻¹ * (n : ℝ) := by ring
    _ = (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)))⁻¹ := h1inv
    _ = ∏ p ∈ n.primeFactors, ((1 - (1 : ℝ) / (p : ℝ))⁻¹) := by rw [Finset.prod_inv_distrib]
    _ = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hp2 : (2 : ℕ) ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      have hp1 : ((p : ℝ) - 1) ≠ 0 := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp [hp0, hp1]

/-- Every prime factor of `q` is `≤ q`, so the product over the prime factors
is bounded by the product over all primes `≤ q`. -/
private lemma prod_primeFactors_le_prod_primesLE (q : ℕ) :
    (∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) ≤
      ∏ p ∈ q.primesLE, ((p : ℝ) / ((p : ℝ) - 1)) := by
  refine Finset.prod_le_prod_of_subset_of_one_le₀ ?h ?hf0 ?hf1
  · intro p hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hpdvd, hq0⟩
    exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hpdvd, hpp⟩
  · intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    exact le_of_lt (primeRatio_pos p hpp.two_le)
  · intro p hp _hpnot
    have hpp : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    exact primeRatio_one_le p hpp.two_le

/-- **Pointwise totient bound:** if `C ≥ 0` satisfies the global product bound
at every `x ≥ 2`, then for `q ≥ 2`, `1/φ(q) ≤ C·log q / q`. -/
private lemma totient_inv_le_mul_log (C : ℝ) (hCglob : ∀ x : ℝ, 2 ≤ x →
    prodPrimeRatio x ≤ C * Real.log x) {q : ℕ} (hq : 2 ≤ q) :
    (Nat.totient q : ℝ)⁻¹ ≤ C * (Real.log (q : ℝ) / (q : ℝ)) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqq : q ≠ 0 := by omega
  have hprod : (q : ℝ) / (Nat.totient q : ℝ) ≤ C * Real.log (q : ℝ) := by
    calc
      (q : ℝ) / (Nat.totient q : ℝ)
          = ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := totient_div_totient_eq_prod q hqq
      _ ≤ ∏ p ∈ q.primesLE, ((p : ℝ) / ((p : ℝ) - 1)) := prod_primeFactors_le_prod_primesLE q
      _ = prodPrimeRatio (q : ℝ) := by
        unfold prodPrimeRatio
        rw [Nat.floor_natCast]
      _ ≤ C * Real.log (q : ℝ) := hCglob (q : ℝ) hqR
  calc
    (Nat.totient q : ℝ)⁻¹
        = ((q : ℝ) / (Nat.totient q : ℝ)) * (q : ℝ)⁻¹ := by
          field_simp [ne_of_gt hqpos]
    _ ≤ (C * Real.log (q : ℝ)) * (q : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr (le_of_lt hqpos))
    _ = C * (Real.log (q : ℝ) / (q : ℝ)) := by
      field_simp [ne_of_gt hqpos]

/-! ## The harmonic-sum estimate `Σ_{q ≤ Q} 1/q ≤ 1 + log Q` -/

/-- The real harmonic partial sum equals the rational `harmonic` from Mathlib. -/
private lemma sum_Icc_one_inv_eq_harmonic (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ)) = (harmonic Q : ℝ) := by
  calc
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ))
        = ∑ q ∈ Finset.Icc 1 Q, (q : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hq0 : (q : ℝ) ≠ 0 := by
            have hq1 : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
            exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq1))
          field_simp [hq0]
    _ = ∑ q ∈ Finset.Icc 1 Q, (((q : ℚ)⁻¹ : ℚ) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          simp
    _ = (harmonic Q : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          exact (Rat.cast_sum (Finset.Icc 1 Q) (fun i : ℕ => ((i : ℚ)⁻¹))).symm

/-- `Σ_{q ∈ Icc 1 Q} 1/q ≤ 1 + log Q`. -/
private lemma harm_Icc_le_one_add_log (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ)) ≤ 1 + Real.log (Q : ℝ) := by
  rw [sum_Icc_one_inv_eq_harmonic]
  exact harmonic_le_one_add_log Q

/-! ## Assembling the main bound -/

/-- `Icc 1 Q = insert 1 (Icc 2 Q)` for `2 ≤ Q`. -/
private lemma Icc_one_eq_insert (Q : ℕ) (hQ : 2 ≤ Q) :
    Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
  ext q
  constructor
  · intro hq
    rw [Finset.mem_insert]
    rcases Finset.mem_Icc.mp hq with ⟨h1q, hqQ⟩
    by_cases h : q = 1
    · left
      exact h
    · right
      exact Finset.mem_Icc.mpr ⟨by omega, hqQ⟩
  · intro hq
    rw [Finset.mem_insert] at hq
    rcases hq with hq1 | hqrest
    · subst q
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · rcases Finset.mem_Icc.mp hqrest with ⟨h2q, hqQ⟩
      exact Finset.mem_Icc.mpr ⟨by omega, hqQ⟩

/-- `log q ≤ log Q` for `q ∈ Icc 1 Q`. -/
private lemma log_le_log_of_mem_Icc {q Q : ℕ} (hq : q ∈ Finset.Icc 1 Q) :
    Real.log (q : ℝ) ≤ Real.log (Q : ℝ) := by
  rcases Finset.mem_Icc.mp hq with ⟨h1, hQq⟩
  exact Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) h1))
    (by exact_mod_cast hQq)

/-- `Σ_{q ∈ Icc 2 Q} log q / q ≤ log Q · Σ_{q ∈ Icc 1 Q} 1/q`. -/
private lemma sum_log_div_self_le (Q : ℕ) :
    (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) ≤
      Real.log (Q : ℝ) * (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ)) := by
  calc
    (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ))
        ≤ ∑ q ∈ Finset.Icc 1 Q, Real.log (q : ℝ) / (q : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
          · intro q hq
            rcases Finset.mem_Icc.mp hq with ⟨h2, hQq⟩
            exact Finset.mem_Icc.mpr ⟨by omega, hQq⟩
          · intro q hq _hnot
            have h1q : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
            have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast h1q)
            have hden : 0 < (q : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1q)
            exact div_nonneg hlog (le_of_lt hden)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, Real.log (Q : ℝ) * (q : ℝ)⁻¹ := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hlelog : Real.log (q : ℝ) ≤ Real.log (Q : ℝ) := log_le_log_of_mem_Icc hq
          have hqinv : 0 ≤ (q : ℝ)⁻¹ := by
            have h1q : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
            have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1q)
            exact inv_nonneg.mpr (le_of_lt hqpos)
          have hle1 : Real.log (q : ℝ) / (q : ℝ) ≤ Real.log (Q : ℝ) * (q : ℝ)⁻¹ := by
            calc
              Real.log (q : ℝ) / (q : ℝ) = Real.log (q : ℝ) * (q : ℝ)⁻¹ := by
                rw [div_eq_mul_inv]
              _ ≤ Real.log (Q : ℝ) * (q : ℝ)⁻¹ := by
                exact mul_le_mul_of_nonneg_right hlelog hqinv
          exact hle1
    _ = Real.log (Q : ℝ) * (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ = Real.log (Q : ℝ) * (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q : ℝ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro q hq
          have h1q : (1 : ℕ) ≤ q := (Finset.mem_Icc.mp hq).1
          have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1q)
          field_simp [ne_of_gt hqpos]

theorem sum_inv_totient_Icc_le_powLog :
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : ℕ, 2 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ)⁻¹)) ≤ C * (Real.log (Q : ℝ)) ^ 2 := by
  obtain ⟨Cg, hCgpos, hCglob⟩ := prodPrimeRatio_le_mul_log
  let ℓ : ℝ := Real.log 2
  have hℓpos : 0 < ℓ := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := 1 / ℓ ^ 2 + Cg * (1 + 1 / ℓ)
  refine ⟨C, ?_, ?_⟩
  · have h1 : 0 < 1 / ℓ ^ 2 := by positivity
    have h2 : 0 ≤ Cg * (1 + 1 / ℓ) := by
      exact mul_nonneg (le_of_lt hCgpos) (by positivity)
    dsimp [C]
    linarith
  · intro Q hQ
    have hQ1 : (1 : ℕ) ≤ Q := by omega
    have hℓleQ : ℓ ≤ Real.log (Q : ℝ) := by
      dsimp [ℓ]
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast (by omega : (2 : ℕ) ≤ Q))
    have hlogQpos : 0 < Real.log (Q : ℝ) := lt_of_lt_of_le hℓpos hℓleQ
    have hnot : (1 : ℕ) ∉ Finset.Icc 2 Q := by
      intro h1in
      have h2le1 : (2 : ℕ) ≤ 1 := (Finset.mem_Icc.mp h1in).1
      omega
    -- split the `q = 1` term
    have hsplit : (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ)⁻¹)) =
        1 + ∑ q ∈ Finset.Icc 2 Q, ((Nat.totient q : ℝ)⁻¹) := by
      rw [Icc_one_eq_insert Q hQ, Finset.sum_insert hnot]
      simp [Nat.totient_one]
    -- bound the terms `q ≥ 2`
    have hsumtot : (∑ q ∈ Finset.Icc 2 Q, ((Nat.totient q : ℝ)⁻¹)) ≤
        Cg * (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) := by
      calc
        (∑ q ∈ Finset.Icc 2 Q, ((Nat.totient q : ℝ)⁻¹))
            ≤ ∑ q ∈ Finset.Icc 2 Q, Cg * (Real.log (q : ℝ) / (q : ℝ)) := by
              refine Finset.sum_le_sum ?_
              intro q hq
              exact totient_inv_le_mul_log Cg (fun x hx => hCglob x hx)
                (Finset.mem_Icc.mp hq).1
        _ = Cg * (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) := by
              rw [Finset.mul_sum]
    -- harmonic bound on the log-sum
    have hlogsum : Cg * (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) ≤
        Cg * (Real.log (Q : ℝ) * (1 + Real.log (Q : ℝ))) := by
      have hle := sum_log_div_self_le Q
      have hharm := harm_Icc_le_one_add_log Q
      have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := le_of_lt hlogQpos
      have hstep : (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) ≤
          Real.log (Q : ℝ) * (1 + Real.log (Q : ℝ)) := le_trans hle (mul_le_mul_of_nonneg_left hharm hlogQ0)
      exact mul_le_mul_of_nonneg_left hstep (le_of_lt hCgpos)
    -- final: polynomial in `u = log Q`
    let u : ℝ := Real.log (Q : ℝ)
    have hu : ℓ ≤ u := by simpa [u, ℓ] using hℓleQ
    have hu0 : 0 ≤ u := le_of_lt (by simpa [u] using hlogQpos)
    have h1 : (1 : ℝ) ≤ (1 / ℓ ^ 2) * u ^ 2 := by
      have hu2 : ℓ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (le_of_lt hℓpos) hu 2
      have hle : (1 : ℝ) ≤ u ^ 2 / ℓ ^ 2 := by
        rw [le_div_iff₀ (by positivity : 0 < ℓ ^ 2)]
        simpa using hu2
      calc (1 : ℝ) ≤ u ^ 2 / ℓ ^ 2 := hle
        _ = (1 / ℓ ^ 2) * u ^ 2 := by ring
    have hpoly : u * (1 + u) ≤ (1 + 1 / ℓ) * u ^ 2 := by
      have hdiff : (1 + 1 / ℓ) * u ^ 2 - u * (1 + u) = (u * (u - ℓ)) / ℓ := by
        field_simp [ne_of_gt hℓpos]
        ring
      have huℓ : 0 ≤ u * (u - ℓ) := mul_nonneg hu0 (sub_nonneg.mpr hu)
      have hsubpos : 0 ≤ (1 + 1 / ℓ) * u ^ 2 - u * (1 + u) := by
        rw [hdiff]
        exact div_nonneg huℓ (le_of_lt hℓpos)
      exact le_of_sub_nonneg hsubpos
    have h3 : Cg * (u * (1 + u)) ≤ Cg * (1 + 1 / ℓ) * u ^ 2 := by
      have hCp : 0 ≤ Cg := le_of_lt hCgpos
      calc
        Cg * (u * (1 + u)) ≤ Cg * ((1 + 1 / ℓ) * u ^ 2) := mul_le_mul_of_nonneg_left hpoly hCp
        _ = Cg * (1 + 1 / ℓ) * u ^ 2 := by ring
    have hbig : 1 + Cg * (u * (1 + u)) ≤ (1 / ℓ ^ 2 + Cg * (1 + 1 / ℓ)) * u ^ 2 := by
      nlinarith [h1, h3]
    calc
      (∑ q ∈ Finset.Icc 1 Q, ((Nat.totient q : ℝ)⁻¹))
          = 1 + ∑ q ∈ Finset.Icc 2 Q, ((Nat.totient q : ℝ)⁻¹) := hsplit
      _ ≤ 1 + Cg * (∑ q ∈ Finset.Icc 2 Q, Real.log (q : ℝ) / (q : ℝ)) := by
            exact add_le_add_right hsumtot 1
      _ ≤ 1 + Cg * (Real.log (Q : ℝ) * (1 + Real.log (Q : ℝ))) := by
            exact add_le_add_right hlogsum 1
      _ = 1 + Cg * (u * (1 + u)) := by
            dsimp [u]
      _ ≤ (1 / ℓ ^ 2 + Cg * (1 + 1 / ℓ)) * u ^ 2 := hbig
      _ = C * (Real.log (Q : ℝ)) ^ 2 := by
            dsimp [C, u]

end

end Commons.NumberTheory.Totient
