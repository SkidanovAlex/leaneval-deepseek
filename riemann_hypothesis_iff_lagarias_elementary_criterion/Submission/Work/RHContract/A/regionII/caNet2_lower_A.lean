import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.MarginDefs
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Commons.NumberTheory.Robin.ca_level_two_lower

/-!
# `caNet2_lower_A` — the `k = 2` net gain is `≥ −5·10⁻⁶` for `3·10⁴ ≤ ξ(ε) < 10⁵`

For a colossally abundant parameter `ε > 0` with largest prime `ξ = caXi ε ∈ [3·10⁴, 10⁵)`
we prove

`Margin.caNet2 ε ≥ −5/10^6`,

where `Margin.caNet2 ε = ∑_{√ξ < p ≤ ξ₂} (caC ε·log p − 1/(2p(p−1)))`, `ξ₂ = Margin.caXi2 ε`
and `caC ε = (1 − 3/√ξ)/(ψ ξ · log ψ ξ)`.

## The argument

Write `n = ⌊√ξ⌋` (so `173 ≤ n ≤ 316`) and `c = caC ε`.  Splitting the summand,

`Net₂ = c·(θ(ξ₂) − θ(n)) − ∑_{n<p≤ξ₂} 1/(2p(p−1))`.

Every prime `p ≤ ⌊1.36 n⌋` satisfies `p ≤ √(2ξ)(1 − log2/(2 log ξ))`, so by
`Commons.NumberTheory.Robin.ca_level_two_lower` its CA exponent is `≥ 2`; hence it is `≤ ξ₂`
(`xi2_ge_cut`).  Cutting the sum at `⌊1.36 n⌋` and discarding the terms above the cut — which
are individually `≥ 0` because `caC ε ≥ (1 − 3/n)/((n²+5n+3)·11.53)` and
`.36·n ≤ p` forces `caC ε·log p ≥ 1/(2p(p−1))` (`caC_mul_log_ge`) — leaves

`Net₂ ≥ c·∑_{n<p≤⌊1.36n⌋} log p − ∑_{n<p≤⌊1.36n⌋} 1/(2p(p−1))`.

The lower bound `c ≥ (1 − 3/n)/((n²+5n+3)·(1153/100))` (`caC_lower`) uses the certified
Chebyshev bounds `θ ξ ≤ ξ`, `ψ ξ − θ ξ ≤ 3√ξ` together with `log(ψ ξ) ≤ 11.53`
(`ψ ξ ≤ 101250 = 2·3⁴·5⁴`).  For the primes above the cut, `log p ≥ ⌊log₂ p⌋·log 2`
(`if_lt_256_log_lower`) while `1/(2p(p−1)) ≤ ⌈10¹²/(2p(p−1))⌉/10¹²`
(`inv_two_mul_le_ceil`), which turns everything into the two *prefix sums over primes*

  `Qkd N = ∑_{p ≤ N, p prime} ⌊log₂ p⌋`,   `Qks N = ∑_{p ≤ N, p prime} ⌈10¹²/(2p(p−1))⌉`,

and a rational inequality `Kd n * 693147 * 10⁶ / 10⁶ ≥ Ks n / 10¹² − 5·10⁻⁶` whose cleared
form `canet2_core_nat` is a finite check, discharged by `interval_cases n <;> decide`
(`canet2_core_nat`) and transported to `ℝ` (`canet2_core`).
-/

namespace Work.RHContract.A.regionII

open Finset

def Qkd : ℕ → ℕ
  | 0 => 0
  | (k+1) => Qkd k + (if Nat.Prime (k+1) then (if k+1 < 256 then 7 else 8) else 0)

def Qks : ℕ → ℕ
  | 0 => 0
  | (k+1) => Qks k + (if Nat.Prime (k+1) then ((10^12 + 2*(k+1)*((k+1)-1) - 1)/(2*(k+1)*((k+1)-1))) else 0)

def Kd (n : ℕ) : ℕ := Qkd (136*n/100) - Qkd n

def Ks (n : ℕ) : ℕ := Qks (136*n/100) - Qks n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma canet2_core_nat (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 316) :
    Ks n * n * (n^2+5*n+3) * 1153
      ≤ 100*(n-3)*Kd n*693147*10^6 + 5*10^6*n*(n^2+5*n+3)*1153 := by
  interval_cases n <;> decide

lemma Qkd_mono : Monotone Qkd := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [Qkd]
  split <;> exact Nat.le_add_right _ _

lemma Qks_mono : Monotone Qks := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [Qks]
  split <;> exact Nat.le_add_right _ _

lemma Qkd_eq_sum_if (N : ℕ) :
    (∑ p ∈ Finset.range (N+1), (if Nat.Prime p then (if p < 256 then 7 else 8) else 0)) = Qkd N := by
  induction N with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Qkd]

lemma Qks_eq_sum_if (N : ℕ) :
    (∑ p ∈ Finset.range (N+1), (if Nat.Prime p then ((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1))) else 0)) = Qks N := by
  induction N with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Qks]

lemma Qkd_eq_sum (N : ℕ) :
    Qkd N = ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (if p < 256 then 7 else 8) := by
  rw [← Qkd_eq_sum_if, Finset.sum_filter]

lemma Qks_eq_sum (N : ℕ) :
    Qks N = ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, ((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1))) := by
  rw [← Qks_eq_sum_if, Finset.sum_filter]

lemma canet2_core_cleared (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 316) :
    (Ks n : ℝ) * (n:ℝ) * ((n:ℝ)^2 + 5*(n:ℝ) + 3) * 1153
      ≤ 100 * ((n:ℝ) - 3) * (Kd n : ℝ) * 693147 * 10^6
        + 5*10^6 * (n:ℝ) * ((n:ℝ)^2 + 5*(n:ℝ) + 3) * 1153 := by
  have h := canet2_core_nat n h1 h2
  have hn3 : 3 ≤ n := by omega
  have hcast3 : ((n - 3 : ℕ) : ℝ) = (n:ℝ) - 3 := by rw [Nat.cast_sub hn3]; norm_num
  have hR0 : ((Ks n * n * (n^2+5*n+3) * 1153 : ℕ) : ℝ)
      ≤ ((100*(n-3)*Kd n*693147*10^6 + 5*10^6*n*(n^2+5*n+3)*1153 : ℕ) : ℝ) := by
    exact_mod_cast h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hR0
  rw [hcast3] at hR0
  exact hR0

lemma canet2_core (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 316) :
    (Ks n : ℝ)/10^12 - 5/10^6
      ≤ ((1 - 3/(n:ℝ)) / (((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100))) * ((Kd n : ℝ) * (693147/10^6)) := by
  have hR := canet2_core_cleared n h1 h2
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hD : (0:ℝ) < (n:ℝ) * ((n:ℝ)^2 + 5*(n:ℝ) + 3) * 1153 := by positivity
  have h10 : (0:ℝ) < 10^12 := by norm_num
  have e2 : (((1 - 3/(n:ℝ)) / (((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100))) * ((Kd n : ℝ) * (693147/10^6)) + 5/10^6) * 10^12
      = ((n:ℝ) - 3) * (Kd n : ℝ) * 693147 * 10^8 / ((n:ℝ) * ((n:ℝ)^2 + 5*(n:ℝ) + 3) * 1153) + 5*10^6 := by
    field_simp
    ring
  rw [sub_le_iff_le_add, div_le_iff₀ h10, e2, ← sub_le_iff_le_add, le_div_iff₀ hD]
  linarith [hR]

lemma if_lt_256_log_lower (p : ℕ) (h1 : 128 ≤ p) (h2 : p < 512) :
    ((if p < 256 then 7 else 8 : ℕ) : ℝ) * (693147/10^6) ≤ Real.log (p:ℝ) := by
  have hlog2 : (693147/10^6 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h128 : (128:ℝ) ≤ (p:ℝ) := by exact_mod_cast h1
  by_cases h : p < 256
  · rw [if_pos h]
    have hlog128 : Real.log ((2:ℝ)^7) = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have h128eq : ((128:ℕ):ℝ) = (2:ℝ)^7 := by norm_num
    calc ((7:ℕ):ℝ) * (693147/10^6) = 7 * (693147/10^6 : ℝ) := by norm_num
      _ ≤ 7 * Real.log 2 := by linarith [hlog2]
      _ = Real.log ((128:ℕ):ℝ) := by rw [h128eq, hlog128]
      _ ≤ Real.log (p:ℝ) := Real.log_le_log (by norm_num) h128
  · rw [if_neg h]
    have h256n : 256 ≤ p := by omega
    have h256 : (256:ℝ) ≤ (p:ℝ) := by exact_mod_cast h256n
    have hlog256 : Real.log ((2:ℝ)^8) = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have h256eq : ((256:ℕ):ℝ) = (2:ℝ)^8 := by norm_num
    calc ((8:ℕ):ℝ) * (693147/10^6) = 8 * (693147/10^6 : ℝ) := by norm_num
      _ ≤ 8 * Real.log 2 := by linarith [hlog2]
      _ = Real.log ((256:ℕ):ℝ) := by rw [h256eq, hlog256]
      _ ≤ Real.log (p:ℝ) := Real.log_le_log (by norm_num) h256

lemma Qkd_cast (N : ℕ) :
    (Qkd N : ℝ) = ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, ((if p < 256 then 7 else 8 : ℕ) : ℝ) := by
  rw [Qkd_eq_sum, Nat.cast_sum]

lemma Qks_cast (N : ℕ) :
    (Qks N : ℝ) = ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1)) : ℕ) : ℝ) := by
  rw [Qks_eq_sum, Nat.cast_sum]

lemma sum_range_primes_add (a b : ℕ) (hab : a ≤ b) (g : ℕ → ℝ) :
    (∑ p ∈ (Finset.range (b+1)).filter Nat.Prime, g p)
      = (∑ p ∈ (Finset.range (a+1)).filter Nat.Prime, g p)
        + (∑ p ∈ (Finset.Icc (a+1) b).filter Nat.Prime, g p) := by
  have hdisj : Disjoint ((Finset.range (a+1)).filter Nat.Prime) ((Finset.Icc (a+1) b).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    simp only [Finset.mem_filter, Finset.mem_range] at hxB
    simp only [Finset.mem_filter, Finset.mem_Icc] at hxC
    omega
  have hunion : (Finset.range (b+1)).filter Nat.Prime
      = ((Finset.range (a+1)).filter Nat.Prime) ∪ ((Finset.Icc (a+1) b).filter Nat.Prime) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨hx, hp⟩
      by_cases h : x ≤ a
      · exact Or.inl ⟨by omega, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨by omega, h3⟩
  rw [hunion, Finset.sum_union hdisj]



/-! ### the CA cut -/

lemma xi2_ge_cut (ε : ℝ) (hε : 0 < ε) (ξ : ℕ) (hξ : ξ = Work.RHPlan.caXi ε)
    (hlo : 30000 ≤ (ξ:ℝ)) (hhi : (ξ:ℝ) < 100000) (n : ℕ)
    (hn1 : (n:ℝ) ≤ Real.sqrt (ξ:ℝ)) :
    ∀ p, Nat.Prime p → p ≤ 136*n/100 → p ≤ Work.RHContract.Margin.caXi2 ε := by
  have hξ30000 : 30000 ≤ ξ := by exact_mod_cast hlo
  have hξne : Work.RHPlan.caXi ε ≠ 0 := by rw [← hξ]; omega
  have hne : (Work.RHPlan.caSupport ε).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    exact hξne (by simp [Work.RHPlan.caXi, hc])
  have hmax : Work.RHPlan.caXi ε = (Work.RHPlan.caSupport ε).max' hne := by
    rw [Work.RHPlan.caXi, Finset.max'_eq_sup', Finset.sup'_eq_sup hne]
  have hmem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε := by
    rw [hmax]; exact Finset.max'_mem _ hne
  have hmem' : Work.RHPlan.caXi ε ∈
      ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
        (fun p : ℕ => 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊) := by
    simpa [Work.RHPlan.caSupport, Work.RHPlan.caMu] using hmem
  obtain ⟨hmem2, hexp⟩ := Finset.mem_filter.mp hmem'
  obtain ⟨hrange, hxi_prime⟩ := Finset.mem_filter.mp hmem2
  rw [Finset.mem_range] at hrange
  have hξ1530 : (1530:ℝ) ≤ (ξ:ℝ) := by linarith
  have hμpos : 0 < Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε := by
    simpa [Work.RHPlan.caMu] using
      Commons.NumberTheory.Robin.caMu_pos (p := Work.RHPlan.caXi ε) (ε := ε) hxi_prime.two_le hε
  have hμ1 : (1:ℝ) ≤ Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε := by
    have h1 : (1:ℝ) ≤ (⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ : ℝ) := by exact_mod_cast hexp
    exact le_trans h1 (Nat.floor_le hμpos.le)
  have hεF : ε ≤ Real.log (((Work.RHPlan.caXi ε : ℝ)^(1+1:ℕ) - 1)/((Work.RHPlan.caXi ε : ℝ)^(1+1:ℕ) - (Work.RHPlan.caXi ε : ℝ)))/Real.log (Work.RHPlan.caXi ε : ℝ) :=
    (Commons.NumberTheory.Robin.caMu_ge_iff_caF (Work.RHPlan.caXi ε) ε 1 hxi_prime.two_le hε le_rfl).mp (by simpa [Work.RHPlan.caMu] using hμ1)
  have heq : Real.log (((Work.RHPlan.caXi ε : ℝ)^(1+1:ℕ) - 1)/((Work.RHPlan.caXi ε : ℝ)^(1+1:ℕ) - (Work.RHPlan.caXi ε : ℝ)))
      = Real.log (1 + 1/(Work.RHPlan.caXi ε : ℝ)) := by
    congr 1
    rw [show (1+1:ℕ) = 2 from rfl, pow_two]
    have h0 : (Work.RHPlan.caXi ε : ℝ) ≠ 0 := by
      rw [← hξ]; exact_mod_cast (show ξ ≠ 0 by omega)
    have h1 : (Work.RHPlan.caXi ε : ℝ) ≠ 1 := by
      rw [← hξ]; exact_mod_cast (show ξ ≠ 1 by omega)
    field_simp
    ring
  rw [heq, ← hξ] at hεF
  have hεξ : ε ≤ Real.log (1 + 1/(ξ:ℝ))/Real.log (ξ:ℝ) := hεF
  have hn316 : n ≤ 316 := by
    have hnsq : ((n:ℝ))^2 ≤ (ξ:ℝ) := by
      rw [← Real.sq_sqrt (by positivity : (0:ℝ) ≤ (ξ:ℝ))]
      exact pow_le_pow_left₀ (by positivity) hn1 2
    by_contra h
    have h317 : 317 ≤ n := by omega
    have h1 : (317:ℝ)^2 ≤ ((n:ℝ))^2 := by
      have h2 : (317:ℝ) ≤ (n:ℝ) := by exact_mod_cast h317
      nlinarith only [h2]
    nlinarith only [hnsq, hhi, h1]
  intro p hp hpcut
  have hn316' : (n:ℝ) ≤ 316 := by exact_mod_cast hn316
  have hp429 : p ≤ 429 := by
    have h45 : 136*n/100 ≤ 429 := by omega
    omega
  have hpn : p < ξ := by omega
  have hlogξ_ge : (9.70:ℝ) ≤ Real.log (ξ:ℝ) := by
    have h2 : (2:ℝ)^14 ≤ (ξ:ℝ) := by
      have h3 : (2:ℕ)^14 ≤ ξ := by norm_num1; omega
      exact_mod_cast h3
    have h14 : (9.70:ℝ) ≤ 14 * Real.log 2 := by nlinarith only [Real.log_two_gt_d9]
    have hlogpow : Real.log ((2:ℝ)^14) = 14 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← hlogpow] at h14
    exact le_trans h14 (Real.log_le_log (by norm_num) h2)
  have hdelta : Real.log 2/(2*Real.log (ξ:ℝ)) ≤ 358/10000 := by
    have hL : (0:ℝ) < Real.log (ξ:ℝ) := by linarith
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * Real.log (ξ:ℝ))]
    nlinarith only [Real.log_two_lt_d9, hlogξ_ge]
  have hsqrt2 : (1.414:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpB : (p:ℝ) ≤ Real.sqrt (2*(ξ:ℝ)) * (1 - Real.log 2/(2*Real.log (ξ:ℝ))) := by
    have hsq2 : Real.sqrt (2*(ξ:ℝ)) = Real.sqrt 2 * Real.sqrt (ξ:ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
    have hsξnn : 0 ≤ Real.sqrt (ξ:ℝ) := Real.sqrt_nonneg _
    have hp1 : (p:ℝ) ≤ (1.36:ℝ)*(n:ℝ) := by
      have h3 : ((136*n/100 : ℕ) : ℝ) ≤ (136:ℝ)*(n:ℝ)/100 := by
        have := Nat.cast_div_le (α := ℝ) (m := 136*n) (n := 100)
        push_cast at this
        exact this
      have h4 : (p:ℝ) ≤ ((136*n/100 : ℕ) : ℝ) := by exact_mod_cast hpcut
      linarith
    have h2 : (1.36:ℝ) * (n:ℝ) ≤ 1.36 * Real.sqrt (ξ:ℝ) := by nlinarith only [hn1]
    have h3 : (Real.sqrt 2 * (1 - Real.log 2/(2*Real.log (ξ:ℝ)))) ≥ 1.36 := by nlinarith only [hsqrt2, hdelta]
    rw [hsq2]
    nlinarith only [hp1, h2, h3, hsξnn]
  have h2 : (2:ℝ) ≤ Work.RHPlan.caMu p ε := by
    have := Commons.NumberTheory.Robin.ca_level_two_lower (ε := ε) (ξ := (ξ:ℝ)) hε hξ1530 hεξ hp hpB
    simpa [Work.RHPlan.caMu] using this
  have hfl : 2 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := Nat.le_floor h2
  have hp_lt : p < Nat.ceil (Real.exp (2 / ε)) + 2 := by
    have h1 : p < Work.RHPlan.caXi ε := by rw [← hξ]; exact hpn
    omega
  have hmem_supp : p ∈ Work.RHPlan.caSupport ε := by
    rw [Work.RHPlan.caSupport]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp_lt, hp⟩, le_trans (by norm_num) hfl⟩
  unfold Work.RHContract.Margin.caXi2
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hmem_supp, hfl⟩)


/-! ### lower bound for `caC` -/

lemma caC_lower (ε : ℝ) (hε : 0 < ε) (ξ : ℕ) (hξ : ξ = Work.RHPlan.caXi ε)
    (hξlo : 30000 ≤ (ξ:ℝ)) (hξhi : (ξ:ℝ) < 100000) (n : ℕ)
    (hn1 : (n:ℝ) ≤ Real.sqrt (ξ:ℝ)) (hnat : ξ ≤ n*n + 2*n) (hn173 : 173 ≤ n) :
    (1 - 3/(n:ℝ)) / (((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) ≤ Work.RHContract.Margin.caC ε := by
  have hξ30000 : 30000 ≤ ξ := by exact_mod_cast hξlo
  have hξ100000 : ξ < 100000 := by exact_mod_cast hξhi
  have hn173' : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn173
  have hnpos : 0 < (n:ℝ) := by linarith
  have htheta : Chebyshev.theta (ξ:ℝ) ≤ (ξ:ℝ) :=
    (Commons.NumberTheory.Chebyshev.theta_bracket_finite_range ξ (by omega) (by omega)).2
  have hpsisub : Chebyshev.psi (ξ:ℝ) - Chebyshev.theta (ξ:ℝ) ≤ 3 * Real.sqrt (ξ:ℝ) :=
    Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt (ξ:ℝ) (by linarith)
  have hpsiub : Chebyshev.psi (ξ:ℝ) ≤ (ξ:ℝ) + 3 * Real.sqrt (ξ:ℝ) := by linarith
  have hcut : (ξ:ℝ) + 3*Real.sqrt (ξ:ℝ) ≤ (n:ℝ)^2 + 5*(n:ℝ) + 3 := by
    have h1 : Real.sqrt (ξ:ℝ) < (n:ℝ) + 1 := by
      rw [Real.sqrt_lt' (by positivity)]
      have hcast : ((n:ℝ)+1)^2 = (((n+1)*(n+1) : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have h2 : ξ < (n+1)*(n+1) := by
        have h3 : (n+1)*(n+1) = n*n + 2*n + 1 := by ring
        rw [h3]; omega
      exact_mod_cast h2
    have h2 : (ξ:ℝ) ≤ (n:ℝ)^2 + 2*(n:ℝ) := by
      have hcast : ((n:ℝ)^2 + 2*(n:ℝ)) = ((n*n + 2*n : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]; exact_mod_cast hnat
    linarith
  have hn316 : n ≤ 316 := by
    have hnsq : ((n:ℝ))^2 ≤ (ξ:ℝ) := by
      rw [← Real.sq_sqrt (by positivity : (0:ℝ) ≤ (ξ:ℝ))]
      exact pow_le_pow_left₀ (by positivity) hn1 2
    by_contra h
    have h317 : 317 ≤ n := by omega
    have h1 : (317:ℝ)^2 ≤ ((n:ℝ))^2 := by
      have h2 : (317:ℝ) ≤ (n:ℝ) := by exact_mod_cast h317
      nlinarith only [h2]
    nlinarith only [hnsq, hξhi, h1]
  have hψlarge : (1:ℝ) < Chebyshev.psi (ξ:ℝ) := by
    have h1 : (9/10:ℝ) * (ξ:ℝ) ≤ Chebyshev.theta (ξ:ℝ) :=
      Commons.NumberTheory.Chebyshev.theta_lower_ninetenths (ξ:ℝ) (by linarith)
    have h2 : (1:ℝ) < Chebyshev.theta (ξ:ℝ) := by nlinarith only [h1, hξlo]
    exact lt_of_lt_of_le h2 (Chebyshev.theta_le_psi _)
  have hpsipos : 0 < Chebyshev.psi (ξ:ℝ) := lt_trans (by norm_num : (0:ℝ) < 1) hψlarge
  have hlogψ : Real.log (Chebyshev.psi (ξ:ℝ)) ≤ 1153/100 := by
    have h1 : Chebyshev.psi (ξ:ℝ) ≤ 101250 := by
      have hs : Real.sqrt (ξ:ℝ) < 317 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
        exact_mod_cast (by omega : ξ < 100489)
      linarith [hpsiub, hξhi]
    have h4 : Real.log (101250:ℝ) ≤ 1153/100 := by
      have he : (101250:ℝ) = 2 * (3:ℝ)^4 * (5:ℝ)^4 := by norm_num
      rw [he, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity),
          Real.log_pow, Real.log_pow]
      push_cast
      nlinarith only [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]
    exact le_trans (Real.log_le_log hpsipos h1) h4
  have hden : Chebyshev.psi (ξ:ℝ) * Real.log (Chebyshev.psi (ξ:ℝ)) ≤ ((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100) := by
    have hlogpos : 0 ≤ Real.log (Chebyshev.psi (ξ:ℝ)) := Real.log_nonneg hψlarge.le
    have h1 : Chebyshev.psi (ξ:ℝ) * Real.log (Chebyshev.psi (ξ:ℝ)) ≤ ((ξ:ℝ) + 3*Real.sqrt (ξ:ℝ)) * (1153/100) :=
      mul_le_mul hpsiub hlogψ hlogpos (by linarith)
    have h2 : ((ξ:ℝ) + 3*Real.sqrt (ξ:ℝ)) * (1153/100) ≤ ((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100) :=
      mul_le_mul_of_nonneg_right hcut (by norm_num)
    linarith
  have hdenpos : 0 < Chebyshev.psi (ξ:ℝ) * Real.log (Chebyshev.psi (ξ:ℝ)) :=
    mul_pos hpsipos (Real.log_pos hψlarge)
  have hnum : 1 - 3/(n:ℝ) ≤ 1 - 3/Real.sqrt (ξ:ℝ) := by
    have h3 : 3/Real.sqrt (ξ:ℝ) ≤ 3/(n:ℝ) := div_le_div_of_nonneg_left (by norm_num) hnpos hn1
    linarith
  have hnumpos : 0 < 1 - 3/(n:ℝ) := by
    have h3 : 3/(n:ℝ) ≤ 3/173 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn173'
    linarith
  have hcaCeq : Work.RHContract.Margin.caC ε
      = (1 - 3/Real.sqrt (ξ:ℝ))/(Chebyshev.psi (ξ:ℝ) * Real.log (Chebyshev.psi (ξ:ℝ))) := by
    unfold Work.RHContract.Margin.caC
    rw [← hξ]
  rw [hcaCeq]
  have hbpos : 0 ≤ 1 - 3/Real.sqrt (ξ:ℝ) := by linarith [hnum, hnumpos.le]
  exact div_le_div₀ hbpos hnum hdenpos hden


/-! ### the per-element rounding bound -/

lemma inv_two_mul_le_ceil (p : ℕ) (hp : 2 ≤ p) :
    (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)) ≤ (((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1)) : ℕ) : ℝ)/10^12 := by
  set D : ℕ := 2*p*(p-1) with hDdef
  have hDn : 0 < D := by
    rw [hDdef]
    have hp1 : 1 ≤ p - 1 := by omega
    have hp0 : 0 < p := by omega
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp0) hp1
  have hceil : 10^12 ≤ D * ((10^12 + D - 1)/D) := by
    have h1 := Nat.div_add_mod (10^12 + D - 1) D
    have h2 := Nat.mod_lt (10^12 + D - 1) hDn
    omega
  have hcast : ((D : ℕ) : ℝ) = 2*(p:ℝ)*((p:ℝ)-1) := by
    rw [hDdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast; ring
  have hDpos : (0:ℝ) < 2*(p:ℝ)*((p:ℝ)-1) := by rw [← hcast]; exact_mod_cast hDn
  have hceilR : (10^12 : ℝ) ≤ (((10^12 + D - 1)/D : ℕ) : ℝ) * (2*(p:ℝ)*((p:ℝ)-1)) := by
    have h : ((10^12 : ℕ) : ℝ) ≤ ((D * ((10^12 + D - 1)/D) : ℕ) : ℝ) := by exact_mod_cast hceil
    push_cast at h
    rw [hcast] at h
    linarith
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10^12), div_mul_eq_mul_div, div_le_iff₀ hDpos]
  linarith [hceilR]


/-! ### the main theorem -/

set_option maxHeartbeats 0 in
/-- For `p > 1.36 n` the `caC`-lower bound already dominates `1/(2p(p-1))`. -/
lemma caC_mul_log_ge (n p : ℕ) (hn : 173 ≤ n) (hn2 : 136*n/100 < p) :
    (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * Real.log (p:ℝ)
      ≥ 1/(2*(p:ℝ)*((p:ℝ)-1)) := by
  have hn173 : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp_p : (1.36:ℝ) * (n:ℝ) < (p:ℝ) := by
    have h1 : (136*n/100 : ℕ) + 1 ≤ p := by omega
    have h2 : 136*n < 100 * ((136*n/100) + 1) := by
      have hm := Nat.div_add_mod (136*n) 100
      have hlt := Nat.mod_lt (136*n) (by norm_num : 0 < 100)
      omega
    have h3 : (136:ℝ)*(n:ℝ) < 100 * (((136*n/100 : ℕ) : ℝ) + 1) := by
      exact_mod_cast h2
    have h4 : (1.36:ℝ)*(n:ℝ) = (136:ℝ)*(n:ℝ)/100 := by ring
    have h5 : ((136*n/100 : ℕ) : ℝ) + 1 ≤ (p:ℝ) := by exact_mod_cast h1
    rw [h4]
    linarith only [h3, h5]
  have hp2 : 2 ≤ p := by omega
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  have hlog : (5.4:ℝ) ≤ Real.log (p:ℝ) := by
    have h225 : (225:ℝ) ≤ (p:ℝ) := by nlinarith only [hn173, hp_p]
    have hlog225 : (5.4:ℝ) ≤ Real.log (225:ℝ) := by
      have he : (225:ℝ) = (3:ℝ)^2 * (5:ℝ)^2 := by norm_num
      rw [he, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      nlinarith only [Real.log_three_gt_d9, Real.log_five_gt_d9]
    exact le_trans hlog225 (Real.log_le_log (by norm_num) h225)
  have hclo : (170/173)/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100))
      ≤ (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) := by
    have hnum : (170/173 : ℝ) ≤ 1 - 3/(n:ℝ) := by
      have h1 : 3/(n:ℝ) ≤ 3/173 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn173
      linarith
    exact div_le_div_of_nonneg_right hnum (by nlinarith only [hn173])
  have hkey : (1:ℝ)/(2*(1.36*(n:ℝ)-1)^2)
      ≤ (170/173)/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * 5.4 := by
    have hD1 : (0:ℝ) < ((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100) := by nlinarith only [hn173]
    have hD2 : (0:ℝ) < 2*(1.36*(n:ℝ)-1)^2 := by nlinarith only [hn173]
    rw [div_mul_eq_mul_div, le_div_iff₀ hD1, div_mul_eq_mul_div, div_le_iff₀ hD2]
    nlinarith only [hn173]
  have hpp : (1:ℝ)/(2*(p:ℝ)*((p:ℝ)-1)) ≤ 1/(2*(1.36*(n:ℝ)-1)^2) := by
    apply div_le_div_of_nonneg_left (by norm_num)
    · nlinarith only [hn173]
    · nlinarith only [hp_p, hpR]
  have h1 : (1:ℝ)/(2*(1.36*(n:ℝ)-1)^2) ≤ (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * 5.4 :=
    le_trans hkey (mul_le_mul_of_nonneg_right hclo (by norm_num))
  have h2 : (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * 5.4
      ≤ (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * Real.log (p:ℝ) := by
    apply mul_le_mul_of_nonneg_left hlog
    have : 3/(n:ℝ) ≤ 3/173 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn173
    apply div_nonneg _ (by nlinarith only [hn173])
    linarith
  linarith [h1, h2, hpp]

/-! ### the main theorem -/

set_option maxHeartbeats 0 in
theorem caNet2_lower_A (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000) :
    -(5/10^6 : ℝ) ≤ Work.RHContract.Margin.caNet2 ε := by
  set ξ : ℕ := Work.RHPlan.caXi ε with hξdef
  set n : ℕ := ⌊Real.sqrt (ξ:ℝ)⌋₊ with hndef
  set M : ℕ := Work.RHContract.Margin.caXi2 ε with hMdef
  set c : ℝ := Work.RHContract.Margin.caC ε with hcdef
  have hξloR : (30000:ℝ) ≤ (ξ:ℝ) := hlo
  have hξhiR : (ξ:ℝ) < 100000 := hhi
  have hn1 : (n:ℝ) ≤ Real.sqrt (ξ:ℝ) := by
    rw [hndef]; exact Nat.floor_le (Real.sqrt_nonneg _)
  have hnsq : ((n:ℝ))^2 ≤ (ξ:ℝ) := by
    rw [← Real.sq_sqrt (by positivity : (0:ℝ) ≤ (ξ:ℝ))]
    exact pow_le_pow_left₀ (by positivity) hn1 2
  have hn_lt : (ξ:ℝ) < ((n:ℝ)+1)^2 := by
    rw [hndef]
    have h1 : Real.sqrt (ξ:ℝ) < ((⌊Real.sqrt (ξ:ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (Real.sqrt (ξ:ℝ))^2 < (((⌊Real.sqrt (ξ:ℝ)⌋₊ : ℕ) : ℝ) + 1)^2 :=
      pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (by norm_num : (2:ℕ) ≠ 0)
    rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (ξ:ℝ))] at h2
  have hξ30000 : 30000 ≤ ξ := by exact_mod_cast hlo
  have hnlo : 173 ≤ n := by
    rw [hndef]
    apply Nat.le_floor
    rw [Real.le_sqrt (by norm_num) (by positivity : (0:ℝ) ≤ (ξ:ℝ))]
    norm_num
    exact_mod_cast (by omega : 29929 ≤ ξ)
  have hnhi : n ≤ 316 := by
    by_contra h
    have h317 : 317 ≤ n := by omega
    have h1 : (317:ℝ)^2 ≤ ((n:ℝ))^2 := by
      have h2 : (317:ℝ) ≤ (n:ℝ) := by exact_mod_cast h317
      nlinarith only [h2]
    nlinarith only [hnsq, hξhiR, h1]
  have hn173' : (173:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnlo
  have hnat : ξ ≤ n*n + 2*n := by
    have h1 : ξ < (n+1)*(n+1) := by
      have hcast : ((n:ℝ)+1)^2 = (((n+1)*(n+1) : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at hn_lt
      exact_mod_cast hn_lt
    have h2 : (n+1)*(n+1) = n*n + 2*n + 1 := by ring
    rw [h2] at h1
    omega
  have hcaNet2 : Work.RHContract.Margin.caNet2 ε
      = ∑ p ∈ (Nat.primesLE M).filter (fun q => n < q),
          (c * Real.log (p:ℝ) - 1/(2*(p:ℝ)*((p:ℝ)-1))) := by
    unfold Work.RHContract.Margin.caNet2
    rw [← hξdef, ← hndef, ← hcdef, ← hMdef]
  by_cases hMn : M ≤ n
  · rw [hcaNet2]
    have hempty : (Nat.primesLE M).filter (fun q => n < q) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨p, hp⟩
      rw [Finset.mem_filter] at hp
      have := Nat.le_of_mem_primesLE hp.1
      omega
    rw [hempty, Finset.sum_empty]
    norm_num
  · have hcut := xi2_ge_cut ε hε ξ hξdef hξloR hξhiR n hn1
    set S : Finset ℕ := (Nat.primesLE M).filter (fun q => n < q) with hSdef
    set Q : Finset ℕ := (Finset.Icc (n+1) (136*n/100)).filter Nat.Prime with hQdef
    have hQS : Q ⊆ S := by
      intro p hp
      rw [hQdef, Finset.mem_filter] at hp
      obtain ⟨hpIcc, hpprime⟩ := hp
      rw [Finset.mem_Icc] at hpIcc
      rw [hSdef, Finset.mem_filter, Nat.mem_primesLE]
      exact ⟨⟨hcut p hpprime hpIcc.2, hpprime⟩, by omega⟩
    have hprimeS : ∀ p ∈ S, Nat.Prime p := by
      intro p hp
      rw [hSdef, Finset.mem_filter] at hp
      exact (Nat.mem_primesLE.mp hp.1).2
    have hclo : (1 - 3/(n:ℝ)) / (((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) ≤ c := by
      rw [hcdef]
      exact caC_lower ε hε ξ hξdef hξloR hξhiR n hn1 hnat hnlo
    have hclopos : 0 < (1 - 3/(n:ℝ)) / (((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) := by
      apply div_pos
      · have : 3/(n:ℝ) ≤ 3/173 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn173'
        linarith
      · positivity
    have hc0 : 0 ≤ c := le_trans hclopos.le hclo
    have hg : 0 ≤ ∑ p ∈ S \ Q, (c * Real.log (p:ℝ) - 1/(2*(p:ℝ)*((p:ℝ)-1))) := by
      apply Finset.sum_nonneg
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpS, hpQ⟩ := hp
      have hpprime : Nat.Prime p := hprimeS p hpS
      have hpgt : 136*n/100 < p := by
        by_contra hcon
        apply hpQ
        rw [hQdef, Finset.mem_filter]
        refine ⟨Finset.mem_Icc.mpr ⟨?_, by omega⟩, hpprime⟩
        rw [hSdef, Finset.mem_filter, Nat.mem_primesLE] at hpS
        omega
      have h1 := caC_mul_log_ge n p hnlo hpgt
      have h2 : (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * Real.log (p:ℝ) ≤ c * Real.log (p:ℝ) :=
        mul_le_mul_of_nonneg_right hclo (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
      linarith [h1, h2]
    have hQlog : ∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ) * (693147/10^6) ≤ ∑ p ∈ Q, Real.log (p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [hQdef, Finset.mem_filter] at hp
      obtain ⟨hpIcc, hpprime⟩ := hp
      rw [Finset.mem_Icc] at hpIcc
      apply if_lt_256_log_lower p
      · omega
      · omega
    have hKd : (∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ)) = (Kd n : ℝ) := by
      have hnb : n ≤ 136*n/100 := by omega
      have hsplit := sum_range_primes_add n (136*n/100) hnb (fun p => ((if p < 256 then 7 else 8 : ℕ):ℝ))
      rw [← Qkd_cast, ← Qkd_cast] at hsplit
      rw [Kd, Nat.cast_sub (Qkd_mono hnb), hQdef]
      linarith [hsplit]
    have hKs : (∑ p ∈ Q, 1/(2*(p:ℝ)*((p:ℝ)-1))) ≤ (Ks n : ℝ)/10^12 := by
      have hnb : n ≤ 136*n/100 := by omega
      have hsplit := sum_range_primes_add n (136*n/100) hnb
        (fun p => (((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1)) : ℕ) : ℝ))
      rw [← Qks_cast, ← Qks_cast] at hsplit
      have hmain : (∑ p ∈ Q, (((10^12 + 2*p*(p-1) - 1)/(2*p*(p-1)) : ℕ) : ℝ)) = (Ks n : ℝ) := by
        rw [Ks, Nat.cast_sub (Qks_mono hnb), hQdef]
        linarith [hsplit]
      rw [← hmain, Finset.sum_div]
      apply Finset.sum_le_sum
      intro p hp
      rw [hQdef, Finset.mem_filter] at hp
      exact inv_two_mul_le_ceil p hp.2.two_le
    have hcore := canet2_core n hnlo hnhi
    have hC : ∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ) * (693147/10^6)
        = (Kd n : ℝ) * (693147/10^6) := by rw [← hKd, Finset.sum_mul]
    have hstep : Work.RHContract.Margin.caNet2 ε
        ≥ c * (∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ) * (693147/10^6)) - (Ks n : ℝ)/10^12 := by
      rw [hcaNet2]
      rw [← Finset.union_sdiff_of_subset hQS, Finset.sum_union Finset.disjoint_sdiff]
      have hQsum2 : ∑ p ∈ Q, (c * Real.log (p:ℝ) - 1/(2*(p:ℝ)*((p:ℝ)-1)))
          = c * (∑ p ∈ Q, Real.log (p:ℝ)) - ∑ p ∈ Q, 1/(2*(p:ℝ)*((p:ℝ)-1)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hQsum2]
      have hm : c * (∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ) * (693147/10^6))
          ≤ c * (∑ p ∈ Q, Real.log (p:ℝ)) := mul_le_mul_of_nonneg_left hQlog hc0
      linarith [hm, hKs, hg]
    have hfinal : c * (∑ p ∈ Q, ((if p < 256 then 7 else 8 : ℕ):ℝ) * (693147/10^6)) - (Ks n : ℝ)/10^12
        ≥ -(5/10^6) := by
      rw [hC]
      have hB : (1 - 3/(n:ℝ))/(((n:ℝ)^2 + 5*(n:ℝ) + 3) * (1153/100)) * ((Kd n : ℝ) * (693147/10^6))
          ≤ c * ((Kd n : ℝ) * (693147/10^6)) :=
        mul_le_mul_of_nonneg_right hclo (by positivity)
      linarith [hB, hcore]
    linarith [hstep, hfinal]

end Work.RHContract.A.regionII
