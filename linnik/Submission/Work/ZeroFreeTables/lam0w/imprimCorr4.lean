/-
# `Work.ZeroFreeTables.lam0w.imprimCorr4`

The imprimitive correction of HB §9: for a non-principal Dirichlet character `χ` of level `q`
and scale `L ≥ log q`, the `P₃`-sum `Σ(s,χ)` at `s = 1 + a/L` is at most the corresponding sum
for the primitive character `χ.primitiveCharacter` (of level `χ.conductor`, the same `L`), plus
the error `(a+λ₁)·e`.

The proof: `SigmaP3L_changeLevel_diff` bounds the difference
`|Σ_q,L(changeLevel χ*) − Σ_N,L(χ*)|` by `(C/L)·(α S₁ + (α²/L) S₂ + (α³/L²) S₃)` where
`S_j = ∑_{p | q} (log p)^j/p`; the prime sums are `O((log log q)^{j+1})` uniformly, and
`log log q ≤ log L`, so the whole correction is `o(1)` as `L → ∞`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.P9.large_prime_factors_sum_le
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le

open scoped BigOperators

namespace Work.ZeroFreeTables.lam0w

open DirichletCharacter

private lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three

/-- `∑_{p | q} (log p)^j / p ≤ C · (log (log q + 2) + 2)^{j+1}` for `j ≤ 3`, uniformly in `q ≥ 1`. -/
theorem pfLogLogBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 1 ≤ q → ∀ j : ℕ, j ≤ 3 →
      ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ C * (Real.log (Real.log (q : ℝ) + 2) + 2) ^ (j + 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 0 (by norm_num)
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  refine ⟨C0 + C1 + C2 + C3 + 1, by linarith only [hC0pos, hC1pos, hC2pos, hC3pos], ?_⟩
  intro q hq j hj
  set C : ℝ := C0 + C1 + C2 + C3 + 1 with hCdef
  set LL : ℝ := Real.log (Real.log (q : ℝ) + 2) + 2 with hLLdef
  have hLL1 : 1 ≤ LL := by
    rw [hLLdef]
    have h1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    have h2 : 0 < Real.log (Real.log (q : ℝ) + 2) := Real.log_pos (by linarith only [h1])
    linarith only [h2]
  have hLLnn : 0 ≤ LL := le_trans zero_le_one hLL1
  have hCle : C0 ≤ C := by rw [hCdef]; linarith only [hC1pos, hC2pos, hC3pos]
  have hC2le : C1 ≤ C := by rw [hCdef]; linarith only [hC0pos, hC2pos, hC3pos]
  have hC3le : C2 ≤ C := by rw [hCdef]; linarith only [hC0pos, hC1pos, hC3pos]
  have hC4le : C3 ≤ C := by rw [hCdef]; linarith only [hC0pos, hC1pos, hC2pos]
  have hCge1 : 1 ≤ C := by rw [hCdef]; linarith only [hC0pos, hC1pos, hC2pos, hC3pos]
  by_cases hq3 : 3 ≤ q
  · have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have hllq_nn : 0 ≤ Real.log (Real.log (q : ℝ)) := by
      apply Real.log_nonneg
      have h3 : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq3R
      linarith only [one_lt_log_three, h3]
    have hllq_le : Real.log (Real.log (q : ℝ)) ≤ LL := by
      rw [hLLdef]
      have hqpos : 0 < Real.log (q : ℝ) := by
        have h3 : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq3R
        linarith only [one_lt_log_three, h3]
      have h : Real.log (Real.log (q : ℝ)) ≤ Real.log (Real.log (q : ℝ) + 2) :=
        Real.log_le_log hqpos (by linarith only [])
      linarith only [h]
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with h0 | h1 | h2 | h3
    · subst h0
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 0 / (p : ℝ)
          ≤ C0 * (Real.log (Real.log (q : ℝ))) ^ (0 + 1) := hC0 q hq3
        _ ≤ C * LL ^ (0 + 1) := by
            have hb : (Real.log (Real.log (q : ℝ))) ^ (0 + 1) ≤ LL ^ (0 + 1) :=
              pow_le_pow_left₀ hllq_nn hllq_le _
            have h2' : C0 * (Real.log (Real.log (q : ℝ))) ^ (0 + 1) ≤ C0 * LL ^ (0 + 1) :=
              mul_le_mul_of_nonneg_left hb hC0pos.le
            have h3' : C0 * LL ^ (0 + 1) ≤ C * LL ^ (0 + 1) :=
              mul_le_mul_of_nonneg_right hCle (pow_nonneg hLLnn _)
            linarith only [h2', h3']
    · subst h1
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 1 / (p : ℝ)
          ≤ C1 * (Real.log (Real.log (q : ℝ))) ^ (1 + 1) := hC1 q hq3
        _ ≤ C * LL ^ (1 + 1) := by
            have hb : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) ≤ LL ^ (1 + 1) :=
              pow_le_pow_left₀ hllq_nn hllq_le _
            have h2' : C1 * (Real.log (Real.log (q : ℝ))) ^ (1 + 1) ≤ C1 * LL ^ (1 + 1) :=
              mul_le_mul_of_nonneg_left hb hC1pos.le
            have h3' : C1 * LL ^ (1 + 1) ≤ C * LL ^ (1 + 1) :=
              mul_le_mul_of_nonneg_right hC2le (pow_nonneg hLLnn _)
            linarith only [h2', h3']
    · subst h2
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)
          ≤ C2 * (Real.log (Real.log (q : ℝ))) ^ (2 + 1) := hC2 q hq3
        _ ≤ C * LL ^ (2 + 1) := by
            have hb : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) ≤ LL ^ (2 + 1) :=
              pow_le_pow_left₀ hllq_nn hllq_le _
            have h2' : C2 * (Real.log (Real.log (q : ℝ))) ^ (2 + 1) ≤ C2 * LL ^ (2 + 1) :=
              mul_le_mul_of_nonneg_left hb hC2pos.le
            have h3' : C2 * LL ^ (2 + 1) ≤ C * LL ^ (2 + 1) :=
              mul_le_mul_of_nonneg_right hC3le (pow_nonneg hLLnn _)
            linarith only [h2', h3']
    · subst h3
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)
          ≤ C3 * (Real.log (Real.log (q : ℝ))) ^ (3 + 1) := hC3 q hq3
        _ ≤ C * LL ^ (3 + 1) := by
            have hb : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) ≤ LL ^ (3 + 1) :=
              pow_le_pow_left₀ hllq_nn hllq_le _
            have h2' : C3 * (Real.log (Real.log (q : ℝ))) ^ (3 + 1) ≤ C3 * LL ^ (3 + 1) :=
              mul_le_mul_of_nonneg_left hb hC3pos.le
            have h3' : C3 * LL ^ (3 + 1) ≤ C * LL ^ (3 + 1) :=
              mul_le_mul_of_nonneg_right hC4le (pow_nonneg hLLnn _)
            linarith only [h2', h3']
  · have hq2 : q ≤ 2 := by omega
    have hsub : q.primeFactors ⊆ ({2} : Finset ℕ) := by
      intro p hp
      have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
      have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
      have hpq' : p ≤ q := Nat.le_of_dvd (by omega) hpq
      have h2 : 2 ≤ p := hpp.two_le
      have : p = 2 := by omega
      simp [this]
    have hsum_le : ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ (Real.log 2) ^ j / 2 := by
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
          ≤ ∑ p ∈ ({2} : Finset ℕ), (Real.log (p : ℝ)) ^ j / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
              rw [Finset.mem_singleton] at hp
              subst hp
              exact div_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) j) (by norm_num))
        _ = (Real.log 2) ^ j / 2 := by simp
    calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ (Real.log 2) ^ j / 2 := hsum_le
      _ ≤ C * LL ^ (j + 1) := by
          have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          have hlog2le1 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith only [h]
          have hnum : (Real.log 2) ^ j ≤ 1 := pow_le_one₀ hlog2nn hlog2le1
          have hLLpow : 1 ≤ LL ^ (j + 1) := one_le_pow₀ hLL1
          have hhalf : (Real.log 2) ^ j / 2 ≤ 1 := by linarith only [hnum]
          calc (Real.log 2) ^ j / 2 ≤ 1 := hhalf
            _ ≤ C * LL ^ (j + 1) := by nlinarith only [hLLpow, hCge1, hC0pos, hC1pos, hC2pos, hC3pos]

/-! ## The analytic core -/

private lemma tendsto_logpow_div (m j : ℕ) (hj : 1 ≤ j) :
    Filter.Tendsto (fun L : ℝ => (Real.log L) ^ m / L ^ j) Filter.atTop (nhds 0) := by
  have hm : Filter.Tendsto (fun L : ℝ => (Real.log L) ^ m / L) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero
  have hinv : Filter.Tendsto (fun L : ℝ => (1 : ℝ) / L) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have hpow : Filter.Tendsto (fun L : ℝ => ((1 : ℝ) / L) ^ (j - 1)) Filter.atTop
      (nhds ((0 : ℝ) ^ (j - 1))) := hinv.pow (j - 1)
  have hmul := hm.mul hpow
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [one_div_pow]
  rw [div_mul_div_comm, mul_one]
  congr 1
  rw [mul_comm L, ← pow_succ, Nat.sub_add_cancel hj]

private lemma tendsto_M2_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 2 / L) Filter.atTop (nhds 0) := by
  have h2 := tendsto_logpow_div 2 1 le_rfl
  have h1 := tendsto_logpow_div 1 1 le_rfl
  have h0 := tendsto_logpow_div 0 1 le_rfl
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 2 / L + 8 * ((Real.log L) ^ 1 / L)
        + 16 * ((Real.log L) ^ 0 / L)) Filter.atTop (nhds 0) := by
    have h' := (h2.add (h1.const_mul 8)).add (h0.const_mul 16)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

private lemma tendsto_M3_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 3 / L ^ 2) Filter.atTop (nhds 0) := by
  have h3 := tendsto_logpow_div 3 2 (by norm_num)
  have h2 := tendsto_logpow_div 2 2 (by norm_num)
  have h1 := tendsto_logpow_div 1 2 (by norm_num)
  have h0 := tendsto_logpow_div 0 2 (by norm_num)
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 3 / L ^ 2 + 12 * ((Real.log L) ^ 2 / L ^ 2)
        + 48 * ((Real.log L) ^ 1 / L ^ 2) + 64 * ((Real.log L) ^ 0 / L ^ 2))
      Filter.atTop (nhds 0) := by
    have h' := ((h3.add (h2.const_mul 12)).add (h1.const_mul 48)).add (h0.const_mul 64)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

private lemma tendsto_M4_div :
    Filter.Tendsto (fun L : ℝ => (Real.log L + 4) ^ 4 / L ^ 3) Filter.atTop (nhds 0) := by
  have h4 := tendsto_logpow_div 4 3 (by norm_num)
  have h3 := tendsto_logpow_div 3 3 (by norm_num)
  have h2 := tendsto_logpow_div 2 3 (by norm_num)
  have h1 := tendsto_logpow_div 1 3 (by norm_num)
  have h0 := tendsto_logpow_div 0 3 (by norm_num)
  have h : Filter.Tendsto
      (fun L : ℝ => (Real.log L) ^ 4 / L ^ 3 + 16 * ((Real.log L) ^ 3 / L ^ 3)
        + 96 * ((Real.log L) ^ 2 / L ^ 3) + 256 * ((Real.log L) ^ 1 / L ^ 3)
        + 256 * ((Real.log L) ^ 0 / L ^ 3)) Filter.atTop (nhds 0) := by
    have h' := (((h4.add (h3.const_mul 16)).add (h2.const_mul 96)).add
      (h1.const_mul 256)).add (h0.const_mul 256)
    simpa using h'
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with L hL
  rw [pow_one, pow_zero]
  field_simp
  ring

/-- The numeric core of the imprimitive correction. -/
theorem corr_numeric {K a e : ℝ} (hK : 0 < K) (ha : 0 < a) (he : 0 < e) {Cpf : ℝ}
    (hCpf : 0 < Cpf) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {L lam₁ LL s1 s2 s3 : ℝ},
      L₀ ≤ L → 0 ≤ LL → LL ≤ Real.log L + 4 → 0 ≤ lam₁ → lam₁ ≤ a →
      s1 ≤ Cpf * LL ^ 2 → s2 ≤ Cpf * LL ^ 3 → s3 ≤ Cpf * LL ^ 4 →
      K * ((1 / L) * ((a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2
        + ((a + lam₁) ^ 3 / L ^ 2) * s3)) ≤ (a + lam₁) * e := by
  let g : ℝ → ℝ := fun L =>
    (Real.log L + 4) ^ 2 / L + (2 * a) * ((Real.log L + 4) ^ 3 / L ^ 2)
      + (4 * a ^ 2) * ((Real.log L + 4) ^ 4 / L ^ 3)
  have hg : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have h' := (tendsto_M2_div.add (tendsto_M3_div.const_mul (2 * a))).add
      (tendsto_M4_div.const_mul (4 * a ^ 2))
    simpa [g] using h'
  have hf : Filter.Tendsto (fun L : ℝ => K * Cpf * g L) Filter.atTop (nhds 0) := by
    simpa using hg.const_mul (K * Cpf)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hf e he
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro L lam₁ LL s1 s2 s3 hL hLL0 hLL hlam0 hlam_a hb1 hb2 hb3
  have hL1le : (1 : ℝ) ≤ L := le_trans (le_max_right N 1) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1le
  have hXnn : 0 ≤ a + lam₁ := by linarith only [ha, hlam0]
  have hX2a : a + lam₁ ≤ 2 * a := by linarith only [hlam_a]
  have hX2 : (a + lam₁) ^ 2 ≤ 4 * a ^ 2 := by
    have h := pow_le_pow_left₀ hXnn hX2a 2
    linarith only [h]
  have hLLpow2 : LL ^ 2 ≤ (Real.log L + 4) ^ 2 := pow_le_pow_left₀ hLL0 hLL 2
  have hLLpow3 : LL ^ 3 ≤ (Real.log L + 4) ^ 3 := pow_le_pow_left₀ hLL0 hLL 3
  have hLLpow4 : LL ^ 4 ≤ (Real.log L + 4) ^ 4 := pow_le_pow_left₀ hLL0 hLL 4
  have hstep3 : (1 / L) * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3 + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)
      ≤ (1 / L) * ((Real.log L + 4) ^ 2 + (2 * a / L) * (Real.log L + 4) ^ 3
          + (4 * a ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_one hLpos.le)
    have hm2 : ((a + lam₁) / L) * LL ^ 3 ≤ (2 * a / L) * (Real.log L + 4) ^ 3 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hLpos.le
      exact mul_le_mul hX2a hLLpow3 (pow_nonneg hLL0 3) (by linarith only [ha])
    have hm3 : ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4 ≤ (4 * a ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg L)
      exact mul_le_mul hX2 hLLpow4 (pow_nonneg hLL0 4) (by positivity)
    linarith only [hLLpow2, hm2, hm3]
  have hs : (a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2 + ((a + lam₁) ^ 3 / L ^ 2) * s3
      ≤ (a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4) := by
    have e1 : (a + lam₁) * s1 ≤ (a + lam₁) * (Cpf * LL ^ 2) :=
      mul_le_mul_of_nonneg_left hb1 hXnn
    have e2 : ((a + lam₁) ^ 2 / L) * s2 ≤ ((a + lam₁) ^ 2 / L) * (Cpf * LL ^ 3) :=
      mul_le_mul_of_nonneg_left hb2 (div_nonneg (sq_nonneg _) hLpos.le)
    have e3 : ((a + lam₁) ^ 3 / L ^ 2) * s3 ≤ ((a + lam₁) ^ 3 / L ^ 2) * (Cpf * LL ^ 4) :=
      mul_le_mul_of_nonneg_left hb3 (div_nonneg (pow_nonneg hXnn 3) (sq_nonneg L))
    have heq : (a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)
        = (a + lam₁) * (Cpf * LL ^ 2) + ((a + lam₁) ^ 2 / L) * (Cpf * LL ^ 3)
          + ((a + lam₁) ^ 3 / L ^ 2) * (Cpf * LL ^ 4) := by ring
    linarith only [e1, e2, e3, heq.le, heq.ge, heq]
  have hgL : g L = (Real.log L + 4) ^ 2 / L + (2 * a) * ((Real.log L + 4) ^ 3 / L ^ 2)
      + (4 * a ^ 2) * ((Real.log L + 4) ^ 4 / L ^ 3) := rfl
  have hN' : K * Cpf * g L < e := by
    have hd := hN L (le_trans (le_max_left N 1) hL)
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_abs_lt hd
  calc K * ((1 / L) * ((a + lam₁) * s1 + ((a + lam₁) ^ 2 / L) * s2
        + ((a + lam₁) ^ 3 / L ^ 2) * s3))
      ≤ K * ((1 / L) * ((a + lam₁) * Cpf * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (div_nonneg zero_le_one hLpos.le))
          hK.le
    _ = (a + lam₁) * (K * Cpf) * ((1 / L) * (LL ^ 2 + ((a + lam₁) / L) * LL ^ 3
          + ((a + lam₁) ^ 2 / L ^ 2) * LL ^ 4)) := by ring
    _ ≤ (a + lam₁) * (K * Cpf) * ((1 / L) * ((Real.log L + 4) ^ 2
          + (2 * a / L) * (Real.log L + 4) ^ 3 + (4 * a ^ 2 / L ^ 2) * (Real.log L + 4) ^ 4)) :=
        mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hXnn (mul_nonneg hK.le hCpf.le))
    _ = (a + lam₁) * (K * Cpf * g L) := by rw [hgL]; ring
    _ ≤ (a + lam₁) * e := mul_le_mul_of_nonneg_left hN'.le hXnn

/-- **The imprimitive correction of HB §9.** -/
theorem imprimCorr4 {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {L lam₁ : ℝ},
      L₀ ≤ L → Real.log (q : ℝ) ≤ L → 0 ≤ lam₁ → lam₁ ≤ a →
      ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 4 →
        Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
          ≤ @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter
              s a lam₁ + (a + lam₁) * e := by
  obtain ⟨C, hCpos, hC⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cpf, hCpfpos, hpf⟩ := pfLogLogBound
  obtain ⟨L0, hL0ge1, hnum⟩ := corr_numeric (K := C) (a := a) (e := e) (Cpf := Cpf) hCpos ha he hCpfpos
  refine ⟨L0, ?_⟩
  intro q hqne χ hχ L lam₁ hL hlogq hlam0 hlam_a s hsre hsim
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL1le : (1 : ℝ) ≤ L := le_trans hL0ge1 hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1le
  have hsy : 1 < s.re := by
    rw [hsre]
    have h : 0 < a / L := div_pos ha hLpos
    linarith only [h]
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdiff := hC (N := χ.conductor) (q := q) (L := L) (s := s) (a := a) (lam₁ := lam₁)
    χ.conductor_dvd_level χ.primitiveCharacter hL1le hsy ha hlam0
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hdiff
  set LL : ℝ := Real.log (Real.log (q : ℝ) + 2) + 2 with hLLdef
  set S1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hS1
  set S2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hS2
  set S3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hS3
  have hLL0 : 0 ≤ LL := by
    rw [hLLdef]
    have h1 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
    have h2 : 0 ≤ Real.log (Real.log (q : ℝ) + 2) := Real.log_nonneg (by linarith only [h1])
    linarith only [h2]
  have hLLle : LL ≤ Real.log L + 4 := by
    rw [hLLdef]
    have h1 : Real.log (q : ℝ) + 2 ≤ 3 * L := by linarith only [hL0ge1, hL, hlogq]
    have h2 : 0 < Real.log (q : ℝ) + 2 := by
      have h : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
      linarith only [h]
    have h3 : Real.log (Real.log (q : ℝ) + 2) ≤ Real.log (3 * L) := Real.log_le_log h2 h1
    have h4 : Real.log (3 * L) = Real.log 3 + Real.log L :=
      Real.log_mul (by norm_num) (ne_of_gt hLpos)
    have h5 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith only [h]
    linarith only [h3, h4, h5]
  have hb1 : S1 ≤ Cpf * LL ^ 2 := by
    rw [hS1, hLLdef]
    simpa [pow_one] using hpf q hq1 1 (by norm_num)
  have hb2 : S2 ≤ Cpf * LL ^ 3 := by
    rw [hS2, hLLdef]
    simpa using hpf q hq1 2 (by norm_num)
  have hb3 : S3 ≤ Cpf * LL ^ 4 := by
    rw [hS3, hLLdef]
    simpa using hpf q hq1 3 (by norm_num)
  have hnum' := hnum hL hLL0 hLLle hlam0 hlam_a hb1 hb2 hb3
  have heq : (C / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
        + ((a + lam₁) ^ 3 / L ^ 2) * S3)
      = C * ((1 / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
        + ((a + lam₁) ^ 3 / L ^ 2) * S3)) := by ring
  have hle : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
      - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L χ.primitiveCharacter
          s a lam₁ ≤ (a + lam₁) * e := by
    have h1 : Work.ZeroFreeTables.SigmaP3L q L χ s a lam₁
        - @Work.ZeroFreeTables.SigmaP3L χ.conductor ⟨χ.conductor_ne_zero⟩ L
            χ.primitiveCharacter s a lam₁
        ≤ (C / L) * ((a + lam₁) * S1 + ((a + lam₁) ^ 2 / L) * S2
            + ((a + lam₁) ^ 3 / L ^ 2) * S3) := le_trans (le_abs_self _) hdiff
    rw [heq] at h1
    exact le_trans h1 hnum'
  linarith only [hle, hqne]

end Work.ZeroFreeTables.lam0w
