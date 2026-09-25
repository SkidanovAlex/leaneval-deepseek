import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Identity.logRatioSum_eq_psiTail
import Submission.Work.RHContract.A.ca_lcmUpto_dvd
import Submission.Work.RHContract.A.ca_delta_nonneg
import Submission.Work.RHContract.Helper.log_taylor_bounds
import Submission.Work.RHContract.Helper.exp_le_caExp
import Submission.Work.RHContract.Helper.log_caNumber_sub_psi_bounds
import Submission.Work.RHContract.Helper.primeTailSummand_le
import Submission.Work.RHContract.A.ca_exp_eq_one_of_gt_xi2
import Submission.Work.RHContract.A.ca_exp_eq_two_of_between

open scoped ArithmeticFunction.sigma
open Finset

namespace Work.RHContract.A

noncomputable section

/-! ## Structural facts about the CA support and `ξ(ε)` -/

/-- The CA support is nonempty as soon as `ξ(ε) ≥ 1530`. -/
lemma caSupport_nonempty (ε : ℝ) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    (Work.RHPlan.caSupport ε).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h0 : Work.RHPlan.caXi ε = 0 := by simp [Work.RHPlan.caXi, h]
  rw [h0] at hξ
  norm_num at hξ

/-- `ξ(ε)` is the maximum of the support. -/
lemma caXi_eq_max' (ε : ℝ) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.caXi ε = (Work.RHPlan.caSupport ε).max' (caSupport_nonempty ε hξ) := by
  rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
  rfl

/-- `ξ(ε)` is prime. -/
lemma caXi_prime (ε : ℝ) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Nat.Prime (Work.RHPlan.caXi ε) := by
  have h := Commons.NumberTheory.Robin.caXi_prime (ε := ε) (caSupport_nonempty ε hξ)
  rw [caXi_eq_max' ε hξ]
  exact h

/-- The support is exactly the set of primes `≤ ξ(ε)`. -/
theorem caSupport_eq_primesLE (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHPlan.caSupport ε = Nat.primesLE (Work.RHPlan.caXi ε) := by
  have hs := caSupport_nonempty ε hξ
  have h1 := Commons.NumberTheory.Robin.caSupp_eq_primesLE_xi (ε := ε) hε hs
  have h2 : Nat.primesLE (Work.RHPlan.caXi ε)
      = (Finset.range ((Work.RHPlan.caXi ε) + 1)).filter Nat.Prime := by
    ext p; rw [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Nat.lt_succ_of_le h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨Nat.le_of_lt_succ h1, h2⟩
  rw [h2, caXi_eq_max' ε hξ]
  exact h1

/-- Membership in the support. -/
lemma mem_caSupport_iff (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} : p ∈ Work.RHPlan.caSupport ε ↔ p ≤ Work.RHPlan.caXi ε ∧ Nat.Prime p := by
  rw [caSupport_eq_primesLE ε hε hξ, Nat.mem_primesLE]

/-- A prime of the support is prime (unconditional form). -/
lemma prime_of_mem_caSupport {ε : ℝ} {p : ℕ} (hp : p ∈ Work.RHPlan.caSupport ε) :
    Nat.Prime p := by
  have h1 : p ∈ ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) :=
    (Finset.mem_filter.mp hp).1
  exact (Finset.mem_filter.mp h1).2

/-- The CA number is the product over the support. -/
lemma caNumber_eq_prod_support (ε : ℝ) :
    Work.RHPlan.caNumber ε
      = ∏ p ∈ Work.RHPlan.caSupport ε, p ^ ⌊Work.RHPlan.caMu p ε⌋₊ := by
  rw [Work.RHPlan.caNumber, Work.RHPlan.caSupport]
  conv_rhs => rw [Finset.prod_filter]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hc : ⌊Work.RHPlan.caMu p ε⌋₊
      = ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ := rfl
  rw [hc]
  by_cases h : 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊
  · simp [h]
  · have hz : ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ = 0 := by omega
    simp [h, hz]

/-- `log(caNumber ε)` as a support sum of `a_p log p`. -/
lemma log_caNumber_eq_sum (ε : ℝ) :
    Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
      = ∑ p ∈ Work.RHPlan.caSupport ε,
          (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) * Real.log (p : ℝ) := by
  rw [caNumber_eq_prod_support, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast (pow_ne_zero _ (prime_of_mem_caSupport hp).pos.ne')

/-- `ψ(ξ(ε))` as a support sum of `e_p log p`. -/
lemma psi_caXi_eq_sum (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)
      = ∑ p ∈ Work.RHPlan.caSupport ε,
          (Nat.log p (Work.RHPlan.caXi ε) : ℝ) * Real.log (p : ℝ) := by
  rw [caSupport_eq_primesLE ε hε hξ]
  exact Chebyshev.psi_eq_sum_mul_log_prime (Work.RHPlan.caXi ε)

/-- The `Δ`-decomposition `log N = ψ(ξ) + Σ (a_p - e_p) log p` is *not* needed as an
equality here; instead we record the difference of the two sums. -/
lemma log_caNumber_sub_psi_eq_sum (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) - Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)
      = ∑ p ∈ Work.RHPlan.caSupport ε,
          ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ))
            * Real.log (p : ℝ) := by
  rw [log_caNumber_eq_sum ε, psi_caXi_eq_sum ε hε hξ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- `ξ₂(ε) ≤ ξ(ε)`. -/
lemma caXi2_le_caXi (ε : ℝ) : Work.RHContract.Margin.caXi2 ε ≤ Work.RHPlan.caXi ε := by
  rw [Work.RHContract.Margin.caXi2, Work.RHPlan.caXi]
  apply Finset.sup_le
  intro p hp
  exact Finset.le_sup (f := id) (Finset.mem_of_mem_filter p hp)

/-! ## The per-prime "correction" term -/

/-- `b_p = -log(1 - p^{-(a_p+1)})`, the negative of the `p`-th correction term of the
`U`-decomposition `caU_decomp`. -/
noncomputable def caB (ε : ℝ) (p : ℕ) : ℝ :=
  -Real.log ((((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
      ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)))

/-- `b_p ≥ 0` for primes `p`. -/
lemma caB_nonneg {ε : ℝ} {p : ℕ} (hp : 2 ≤ p) : 0 ≤ caB ε p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hexp : 1 < (p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1) := one_lt_pow₀ hp1 (by omega)
  have hlt : (((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
      ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hpos : 0 < (((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
      ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) := by
    apply div_pos _ (by positivity); linarith
  unfold caB
  exact neg_nonneg.mpr (le_of_lt (Real.log_neg hpos hlt))

/-- The `caU`-decomposition summand is `-caB`. -/
lemma caU_corr_eq (ε : ℝ) (p : ℕ) :
    Real.log ((((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
        ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1))) = -caB ε p := by
  unfold caB; ring

/-! ## The key decomposition identity -/

/-- `log(σ(N_ε)/N_ε)` expressed through `logRatioSum`: the content of `caU_decomp`
combined with `caMertensSum_eq_logRatioSum_xi` and the Mertens identity. -/
theorem log_sigmaSub_div (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
        / ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
      = Real.eulerMascheroniConstant + Real.log (Real.log (Work.RHPlan.caXi ε : ℝ))
        + (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ))
            / ((Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
        - Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ)
        + Work.RHContract.primeTail (Work.RHPlan.caXi ε : ℝ)
        - ∑ p ∈ Work.RHPlan.caSupport ε, caB ε p := by
  have hξ2 : 2 ≤ Work.RHPlan.caXi ε := by
    have : (2 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
    exact_mod_cast this
  have hs := caSupport_nonempty ε hξ
  have hNpos : 0 < Work.RHPlan.caNumber ε := by
    rw [Work.RHPlan.caNumber]
    exact Finset.prod_pos (fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _)
  have hNnz : ((Work.RHPlan.caNumber ε : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hσpos : 0 < ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) :=
    ArithmeticFunction.sigma_pos 1 (Work.RHPlan.caNumber ε) hNpos.ne'
  have hσnz : (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hσpos.ne'
  have hU' : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ))
      - Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)
      = (∑ p ∈ Work.RHPlan.caSupport ε, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
        + ∑ p ∈ Work.RHPlan.caSupport ε,
            Real.log ((((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
              ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1))) := by
    simpa only [Work.RHPlan.caNumber, Work.RHPlan.caSupport, Work.RHPlan.caMu] using
      (Commons.NumberTheory.Robin.caU_decomp (ε := ε) hε)
  have hmax : (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter
      (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) /
        (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).max' hs
      = Work.RHPlan.caXi ε := by
    change (Work.RHPlan.caSupport ε).max' hs = Work.RHPlan.caXi ε
    rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
    rfl
  have hM' : (∑ p ∈ Work.RHPlan.caSupport ε, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
      = Commons.NumberTheory.Mertens.logRatioSum (Work.RHPlan.caXi ε : ℝ) := by
    have h := Commons.NumberTheory.Robin.caMertensSum_eq_logRatioSum_xi (ε := ε) hε hs
    rw [hmax] at h
    simpa only [Work.RHPlan.caSupport, Work.RHPlan.caMu] using h
  have hI := Work.RHContract.Identity.logRatioSum_eq_psiTail (Work.RHPlan.caXi ε : ℝ)
    (by exact_mod_cast hξ2)
  have hcorr : (∑ p ∈ Work.RHPlan.caSupport ε,
        Real.log ((((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) - 1) /
          ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1))))
      = - ∑ p ∈ Work.RHPlan.caSupport ε, caB ε p := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun p _ => caU_corr_eq ε p)
  rw [Real.log_div hσnz hNnz, hU', hM', hI, hcorr]
  ring

/-- **The key identity.**  `γ + logloglog N − log(σ(N)/N) − J(ξ)` equals
`(logloglog N − loglog ψ(ξ)) − W + (Σ b_p − primeTail ξ)`. -/
theorem key_identity (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Real.eulerMascheroniConstant
        + Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
        - Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
            / ((Work.RHPlan.caNumber ε : ℕ) : ℝ))
        - Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ)
      = (Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
          - Real.log (Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ))))
        - Work.RHContract.Margin.caW ε
        + (∑ p ∈ Work.RHPlan.caSupport ε, caB ε p)
        - Work.RHContract.primeTail (Work.RHPlan.caXi ε : ℝ) := by
  rw [log_sigmaSub_div ε hε hξ]
  unfold Work.RHContract.Margin.caW
  ring

/-! ## Abbreviations for the analytic step -/

/-- `ψ(ξ(ε))`. -/
noncomputable def caPsi (ε : ℝ) : ℝ := Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)

/-- `log N_ε`. -/
noncomputable def caLogN (ε : ℝ) : ℝ := Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)

/-- `Δ = log N_ε − ψ(ξ(ε))`. -/
noncomputable def caDelta (ε : ℝ) : ℝ := caLogN ε - caPsi ε

lemma caC_eq (ε : ℝ) :
    Work.RHContract.Margin.caC ε
      = (1 - 3 / Real.sqrt (Work.RHPlan.caXi ε : ℝ)) / (caPsi ε * Real.log (caPsi ε)) := by
  unfold Work.RHContract.Margin.caC caPsi
  rfl

/-- **The log-ratio step.**  For `0 < ε` with `ξ(ε) ≥ 1530` and `Δ = log N_ε − ψ(ξ(ε))` in
`[0, 4 √ξ]`, `logloglog N_ε − loglog ψ(ξ) ≥ caC ε · Δ`.  The saving factor `(1 − 3/√ξ)` in
`caC` absorbs the quadratic errors of `log(1+y) ≥ y − y²/2`. -/
theorem loglog_step (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hP : 0 < Work.RHPlan.caXi ε)
    (hΔ0 : 0 ≤ caDelta ε)
    (hΔU : caDelta ε ≤ 4 * Real.sqrt (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHContract.Margin.caC ε * caDelta ε
      ≤ Real.log (Real.log (caLogN ε)) - Real.log (Real.log (caPsi ε)) := by
  obtain ⟨hlt1, hlt2, hlt3, hlt4, hlt5, hlt6⟩ := Work.RHContract.Helper.log_taylor_bounds
  set ξr : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξrdef
  have hξ_pos : 0 < ξr := by rw [hξrdef]; exact_mod_cast hP
  have hξ1530 : 1530 ≤ ξr := by rw [hξrdef]; exact hξ
  set ψ : ℝ := caPsi ε with hψdef
  have hψ_ge : 9 / 10 * ξr ≤ ψ := by
    rw [hξrdef, hψdef]
    exact le_trans (Commons.NumberTheory.Chebyshev.theta_lower_ninetenths _ hξ)
      (Chebyshev.theta_le_psi _)
  have hψ_pos : 0 < ψ := by linarith
  have hlogψ3 : 3 ≤ Real.log ψ := by
    have h1377 : (0 : ℝ) < 1377 := by norm_num
    have hlog1377 : (3 : ℝ) ≤ Real.log 1377 := by
      rw [Real.le_log_iff_exp_le h1377]
      have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
      rw [h3]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have hle : Real.log 1377 ≤ Real.log ψ := Real.log_le_log h1377 (by linarith)
    linarith
  have hlogψ_pos : 0 < Real.log ψ := by linarith
  set Δ : ℝ := caDelta ε with hΔdef
  have hΔ0' : 0 ≤ Δ := by rw [hΔdef]; exact hΔ0
  have hΔU' : Δ ≤ 4 * Real.sqrt ξr := by
    rw [hΔdef, caDelta, caLogN, caPsi, hξrdef]; exact hΔU
  set t : ℝ := Δ / ψ with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have ht_ub : t ≤ (40 / 9) / Real.sqrt ξr := by
    rw [htdef]
    calc Δ / ψ ≤ (4 * Real.sqrt ξr) / ψ := by
            exact div_le_div_of_nonneg_right hΔU' hψ_pos.le
      _ ≤ (4 * Real.sqrt ξr) / (9 / 10 * ξr) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hψ_ge
      _ = (40 / 9) / Real.sqrt ξr := by
            have hsq : Real.sqrt ξr * Real.sqrt ξr = ξr := Real.mul_self_sqrt hξ_pos.le
            field_simp
            nlinarith [hsq]
  have ht3 : t * (1 / 2) * (1 + 1 / Real.log ψ) ≤ 3 / Real.sqrt ξr := by
    have hb : (1 / 2) * (1 + 1 / Real.log ψ) ≤ 2 / 3 := by
      have h1 : 1 / Real.log ψ ≤ 1 / 3 := by
        rw [div_le_div_iff₀ hlogψ_pos (by norm_num)]
        linarith
      linarith
    calc t * (1 / 2) * (1 + 1 / Real.log ψ)
        = t * ((1 / 2) * (1 + 1 / Real.log ψ)) := by ring
      _ ≤ ((40 / 9) / Real.sqrt ξr) * (2 / 3) := by
            apply mul_le_mul ht_ub hb (by positivity) (by positivity)
      _ = (80 / 27) / Real.sqrt ξr := by ring
      _ ≤ 3 / Real.sqrt ξr := by
            rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hξ_pos) (Real.sqrt_pos.mpr hξ_pos)]
            nlinarith [Real.sqrt_pos.mpr hξ_pos]
  set α : ℝ := Real.log (1 + t) / Real.log ψ with hαdef
  have hα0 : 0 ≤ α := by
    rw [hαdef]; apply div_nonneg
    · exact Real.log_nonneg (by linarith)
    · exact hlogψ_pos.le
  have hαl : (t - t ^ 2 / 2) / Real.log ψ ≤ α := by
    rw [hαdef]
    apply div_le_div_of_nonneg_right _ hlogψ_pos.le
    linarith [hlt2 t ht0]
  have hαu : α ≤ t / Real.log ψ := by
    rw [hαdef]
    apply div_le_div_of_nonneg_right _ hlogψ_pos.le
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + t by linarith)
    linarith
  have hα2 : α ^ 2 ≤ (t / Real.log ψ) ^ 2 :=
    pow_le_pow_left₀ hα0 hαu 2
  have hlog1α : α - α ^ 2 / 2 ≤ Real.log (1 + α) := by
    have h := hlt2 α hα0
    linarith
  have hchain : (t / Real.log ψ) * (1 - 3 / Real.sqrt ξr) ≤ α - α ^ 2 / 2 := by
    have hEq : (t - t ^ 2 / 2) / Real.log ψ - (t / Real.log ψ) ^ 2 / 2
        = (t / Real.log ψ) * (1 - t / 2 - t / (2 * Real.log ψ)) := by
      field_simp <;> ring
    have hExp : (t - t ^ 2 / 2) / Real.log ψ - (t / Real.log ψ) ^ 2 / 2 ≤ α - α ^ 2 / 2 := by
      linarith [hαl, hα2]
    have hstep : (t / Real.log ψ) * (1 - 3 / Real.sqrt ξr)
        ≤ (t - t ^ 2 / 2) / Real.log ψ - (t / Real.log ψ) ^ 2 / 2 := by
      rw [hEq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hsum : t / 2 + t / (2 * Real.log ψ) = t * (1 / 2) * (1 + 1 / Real.log ψ) := by
        field_simp <;> ring
      linarith [ht3, hsum]
    linarith [hstep, hExp]
  have hfinal : Work.RHContract.Margin.caC ε * Δ ≤ Real.log (1 + α) := by
    have hca : Work.RHContract.Margin.caC ε
        = (1 - 3 / Real.sqrt ξr) / (ψ * Real.log ψ) := by
      rw [caC_eq ε, hψdef, hξrdef]
    rw [hca]
    have hrew : (1 - 3 / Real.sqrt ξr) / (ψ * Real.log ψ) * Δ
        = (t / Real.log ψ) * (1 - 3 / Real.sqrt ξr) := by
      rw [htdef]; field_simp <;> ring
    rw [hrew]
    linarith [hchain, hlog1α]
  have hkey : Real.log (Real.log (caLogN ε)) - Real.log (Real.log ψ) = Real.log (1 + α) := by
    have hplus : caLogN ε = ψ + Δ := by
      have hcd : caDelta ε = caLogN ε - caPsi ε := rfl
      rw [hΔdef, hcd, hψdef]; ring
    have h1 : Real.log (caLogN ε) = Real.log ψ + Real.log (1 + t) := by
      rw [hplus, show ψ + Δ = ψ * (1 + Δ / ψ) by field_simp, htdef,
        Real.log_mul (ne_of_gt hψ_pos) (by positivity)]
    have hA : 0 < Real.log ψ + Real.log (1 + t) := by
      have : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
      linarith
    rw [h1, ← Real.log_div hA.ne' (ne_of_gt hlogψ_pos)]
    congr 1
    rw [hαdef]
    field_simp <;> ring
  rw [hkey]
  exact hfinal
/-! ## The per-prime contribution and its three case bounds -/

/-- The `p`-th summand of the final comparison: the CA-exponent gain `caC·(a_p−e_p)·log p`
plus the correction `b_p` minus the prime-tail summand `t_p`. -/
noncomputable def caContrib (ε : ℝ) (p : ℕ) : ℝ :=
  Work.RHContract.Margin.caC ε
      * ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ))
      * Real.log (p : ℝ)
    + caB ε p - Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ)

/-- `primeTail` as a sum over the CA support. -/
lemma primeTail_eq_sum_support (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHContract.primeTail (Work.RHPlan.caXi ε : ℝ)
      = ∑ p ∈ Work.RHPlan.caSupport ε,
          Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ) := by
  rw [Work.RHContract.primeTail_eq_sum, Nat.floor_natCast, ← caSupport_eq_primesLE ε hε hξ]

/-- `caB ε p = -log(1 - 1/p^{a+1})`. -/
lemma caB_eq {ε : ℝ} {p : ℕ} (hp : 2 ≤ p) :
    caB ε p = -Real.log (1 - 1 / (p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1)) := by
  unfold caB
  have hpow : (0 : ℝ) < (p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1) := by
    exact pow_pos (by exact_mod_cast (by omega : 0 < p)) _
  congr 2
  field_simp <;> ring

/-- **(i)** Above `ξ₂`, the contribution dominates `1/(2p²) − 1/(3p³)`. -/
lemma caContrib_ge_large (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h1 : Work.RHContract.Margin.caXi2 ε < p)
    (h2 : p ≤ Work.RHPlan.caXi ε) :
    1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3) ≤ caContrib ε p := by
  obtain ⟨hlt1, _, _, _, _, _⟩ := Work.RHContract.Helper.log_taylor_bounds
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have ha : ⌊Work.RHPlan.caMu p ε⌋₊ = 1 := ca_exp_eq_one_of_gt_xi2 ε hε hξ hp h1 h2
  have he : Nat.log p (Work.RHPlan.caXi ε) = 1 := by
    have hle : Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
      Work.RHContract.Helper.exp_le_caExp ε hε hξ p hp h2
    have hge : 1 ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.log_pos hp.one_lt h2
    omega
  have ht : Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ)
      = -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) := by
    unfold Work.RHContract.primeTailSummand
    rw [Nat.floor_natCast, he]
    simp [Finset.Icc_self]
  have hb : caB ε p = -Real.log (1 - 1 / (p : ℝ) ^ 2) := by
    rw [caB_eq (ε := ε) hp.two_le, ha]
  have hfac : (1 : ℝ) - 1 / (p : ℝ) ^ 2 = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ)) := by
    field_simp <;> ring
  have hpA : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hp0]; exact_mod_cast hp.one_lt
  have hpB : (0 : ℝ) < 1 + 1 / (p : ℝ) := by positivity
  have hl : -Real.log (1 - 1 / (p : ℝ) ^ 2)
      = -Real.log (1 - 1 / (p : ℝ)) - Real.log (1 + 1 / (p : ℝ)) := by
    rw [hfac, Real.log_mul hpA.ne' hpB.ne']
    ring
  have hval : caContrib ε p = 1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ)) := by
    rw [caContrib, ha, he, ht, hb, hl]
    simp only [Nat.cast_one]
    ring_nf
  rw [hval]
  have hkey := hlt1 (1 / (p : ℝ)) (by positivity)
  have e2 : (1 / (p : ℝ)) ^ 2 / 2 = 1 / (2 * (p : ℝ) ^ 2) := by ring
  have e3 : (1 / (p : ℝ)) ^ 3 / 3 = 1 / (3 * (p : ℝ) ^ 3) := by ring
  linarith [hkey, e2, e3]

/-- **(ii)** On `(√ξ, ξ₂]`, the contribution dominates `caC·log p − 1/(2p(p−1))`. -/
lemma caContrib_ge_mid (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h1 : Real.sqrt (Work.RHPlan.caXi ε : ℝ) < (p : ℝ))
    (h2 : p ≤ Work.RHContract.Margin.caXi2 ε) :
    Work.RHContract.Margin.caC ε * Real.log (p : ℝ) - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))
      ≤ caContrib ε p := by
  obtain ⟨_, _, _, _, hlt5, _⟩ := Work.RHContract.Helper.log_taylor_bounds
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpxi : p ≤ Work.RHPlan.caXi ε := le_trans h2 (caXi2_le_caXi ε)
  have hXnz : Work.RHPlan.caXi ε ≠ 0 := by
    intro h0; rw [h0] at hξ; norm_num at hξ
  have ha : ⌊Work.RHPlan.caMu p ε⌋₊ = 2 := ca_exp_eq_two_of_between ε hε hξ hp h1 h2
  have he : Nat.log p (Work.RHPlan.caXi ε) = 1 := by
    have hsq : (p : ℝ) ^ 2 > (Work.RHPlan.caXi ε : ℝ) := by
      have hξ0 : (0 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
        have := caXi_prime ε hξ; exact_mod_cast this.pos.le
      nlinarith [Real.sq_sqrt hξ0, h1, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ), hp0]
    have hE : p ^ 2 > Work.RHPlan.caXi ε := by exact_mod_cast hsq
    have hle : Nat.log p (Work.RHPlan.caXi ε) ≤ 1 := by
      by_contra h
      have h2le : 2 ≤ Nat.log p (Work.RHPlan.caXi ε) := by
        have := Nat.lt_of_not_le h; omega
      have hpow : p ^ 2 ≤ p ^ Nat.log p (Work.RHPlan.caXi ε) :=
        Nat.pow_le_pow_right hp.one_le h2le
      have hself : p ^ Nat.log p (Work.RHPlan.caXi ε) ≤ Work.RHPlan.caXi ε :=
        Nat.pow_log_le_self p hXnz
      exact absurd (lt_of_lt_of_le hE (le_trans hpow hself)) (lt_irrefl _)
    have hge : 1 ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.log_pos hp.one_lt hpxi
    omega
  have ht : Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ)
      = -Real.log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) := by
    unfold Work.RHContract.primeTailSummand
    rw [Nat.floor_natCast, he]
    simp [Finset.Icc_self]
  have hb : caB ε p = -Real.log (1 - 1 / (p : ℝ) ^ 3) := by
    rw [caB_eq (ε := ε) hp.two_le, ha]
  have hfac : (1 : ℝ) - 1 / (p : ℝ) ^ 3
      = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
    field_simp <;> ring
  have hpA : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one hp0]; exact_mod_cast hp.one_lt
  have hpC : (0 : ℝ) < 1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by positivity
  have hl : -Real.log (1 - 1 / (p : ℝ) ^ 3)
      = -Real.log (1 - 1 / (p : ℝ)) - Real.log (1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
    rw [hfac, Real.log_mul hpA.ne' hpC.ne']
    ring
  have hval : caContrib ε p
      = Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
        + (1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2)) := by
    rw [caContrib, ha, he, ht, hb, hl]
    simp only [Nat.cast_two, Nat.cast_one]
    ring_nf
  rw [hval]
  have hu : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hu2 : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have hkey := hlt5 (1 / (p : ℝ)) (by positivity) hu2
  have hkey' : (1 / (p : ℝ)) ^ 3 = 1 / (p : ℝ) ^ 3 := by ring
  have hkey2 : (1 / (p : ℝ)) ^ 2 / (2 * (1 - 1 / (p : ℝ))) = 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) := by
    field_simp <;> ring
  have hlogid : -Real.log (1 - (1 / (p : ℝ)) ^ 3) + Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)
      = 1 / (p : ℝ) - Real.log (1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
    rw [show (1 : ℝ) - (1 / (p : ℝ)) ^ 3 = (1 - 1 / (p : ℝ)) * (1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) from by
      rw [← hfac, hkey']]
    rw [Real.log_mul hpA.ne' hpC.ne']
    ring
  linarith [hkey, hlogid, hkey2]

/-- **(iii)** Below `√ξ`, the contribution dominates minus the `K₃` summand. -/
lemma caContrib_ge_small (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h2 : p ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊) :
    -(max 0 ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
        (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        - Work.RHContract.Margin.caC ε * Real.log (p : ℝ))) ≤ caContrib ε p := by
  obtain ⟨_, _, _, _, _, hlt6⟩ := Work.RHContract.Helper.log_taylor_bounds
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hξ0 : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by
    have := caXi_prime ε hξ; exact_mod_cast this.pos
  have hroot : ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ ≤ Work.RHPlan.caXi ε := by
    have hle : Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := Real.one_le_sqrt.mpr (by linarith)
      nlinarith [Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
    calc ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ ≤ ⌊(Work.RHPlan.caXi ε : ℝ)⌋₊ := Nat.floor_mono hle
      _ = Work.RHPlan.caXi ε := Nat.floor_natCast _
  have hpxi : p ≤ Work.RHPlan.caXi ε := le_trans h2 hroot
  have heS : Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
    Work.RHContract.Helper.exp_le_caExp ε hε hξ p hp hpxi
  have hfloor : Work.RHContract.Margin.caExpFloor ε p = Nat.log p (Work.RHPlan.caXi ε) := by
    unfold Work.RHContract.Margin.caExpFloor
    rw [Nat.floor_natCast]
  have he2 : 2 ≤ Nat.log p (Work.RHPlan.caXi ε) := by
    have hsq : p ^ 2 ≤ Work.RHPlan.caXi ε := by
      have h2' : (p : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
        have h3 : (p : ℝ) ≤ (⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ : ℝ) := by exact_mod_cast h2
        exact le_trans h3 (Nat.floor_le (Real.sqrt_nonneg _))
      have : (p : ℝ) ^ 2 ≤ (Work.RHPlan.caXi ε : ℝ) := by
        nlinarith [h2', Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
      exact_mod_cast this
    calc 2 = Nat.log p (p ^ 2) := by rw [Nat.log_pow hp.one_lt]
      _ ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.log_mono_right hsq
  have ht_bound : Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ)
      ≤ (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
          (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ))) := by
    unfold Work.RHContract.primeTailSummand
    rw [Nat.floor_natCast, hfloor]
    exact Work.RHContract.Helper.primeTailSummand_le p (Nat.log p (Work.RHPlan.caXi ε)) hp.two_le
  have hB0 : 0 ≤ caB ε p := caB_nonneg hp.two_le
  have hcaC0 : 0 ≤ Work.RHContract.Margin.caC ε := by
    unfold Work.RHContract.Margin.caC
    apply div_nonneg
    · have h1 : (3 : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
      have h2 : 3 / Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact h1
      linarith
    · apply mul_nonneg
      · exact Chebyshev.psi_nonneg _
      · apply Real.log_nonneg
        have := Commons.NumberTheory.Chebyshev.theta_lower_ninetenths (Work.RHPlan.caXi ε : ℝ) hξ
        have := Chebyshev.theta_le_psi (Work.RHPlan.caXi ε : ℝ)
        linarith
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hgap : ⌊Work.RHPlan.caMu p ε⌋₊ = Nat.log p (Work.RHPlan.caXi ε) ∨
      Nat.log p (Work.RHPlan.caXi ε) + 1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ := by omega
  have hneg : -(max 0 ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
        (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        - Work.RHContract.Margin.caC ε * Real.log (p : ℝ)))
      ≤ Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
        - (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
          (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ))) := by
    set X : ℝ := Work.RHContract.Margin.caC ε * Real.log (p : ℝ) with hX
    set Y : ℝ := (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
      (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ))) with hY
    have : -(X - Y) = Y - X := by ring
    have hmax : Y - X ≤ max 0 (Y - X) := le_max_right _ _
    linarith [hmax, this]
  rcases hgap with hae | hgt
  · -- a = e
    have hBLE : (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) ≤ caB ε p := by
      rw [hfloor, ← hae, caB_eq (ε := ε) hp.two_le]
      rw [show -(((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) + 1))
          = -(((⌊Work.RHPlan.caMu p ε⌋₊ + 1 : ℕ) : ℝ)) by push_cast; ring]
      rw [Real.rpow_neg (le_of_lt hp0), Real.rpow_natCast]
      have hz := hlt6 ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1))⁻¹ (by positivity)
        (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega)))
      simpa only [one_div] using hz
    have hYle : (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
          (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        ≤ (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) := by
      have hden : (1 : ℝ) ≤ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)) := by
        rw [hfloor]
        have h21 : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
          have : 1 / (p : ℝ) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
          linarith
        have h3 : (3 : ℝ) ≤ (Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1 := by
          have : (2 : ℝ) ≤ (Nat.log p (Work.RHPlan.caXi ε) : ℝ) := by exact_mod_cast he2
          linarith
        nlinarith [mul_le_mul h3 h21 (by norm_num) (by linarith)]
      calc (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
            (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
          ≤ ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)))) / 1 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) := by rw [div_one]
    have hcontrib : 0 ≤ caContrib ε p := by
      have hzero : Work.RHContract.Margin.caC ε *
          ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ) = 0 := by
        rw [hae]; ring
      rw [caContrib, hzero]
      linarith [hBLE, ht_bound, hYle]
    have hmaxnn : 0 ≤ max 0 ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
        (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        - Work.RHContract.Margin.caC ε * Real.log (p : ℝ)) := le_max_left _ _
    linarith [hcontrib, hmaxnn]
  · -- a > e
    have hgain : Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
        ≤ Work.RHContract.Margin.caC ε *
          ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ) := by
      have h1e : (1 : ℝ) ≤ (⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ) := by
        have : (1 : ℕ) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ - Nat.log p (Work.RHPlan.caXi ε) := by omega
        exact_mod_cast this
      have h2e : (0 : ℝ) ≤ Work.RHContract.Margin.caC ε := hcaC0
      have h3e : (0 : ℝ) ≤ Real.log (p : ℝ) := hlogp0
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1e h2e) h3e]
    have hmain : Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
            (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        ≤ caContrib ε p := by
      rw [caContrib]
      linarith [hgain, hB0, ht_bound]
    linarith [hneg, hmain]


/-- The "tail" expression `Y_p = p^{-(e_p+1)}/((e_p+1)(1-1/p))`. -/
noncomputable def caYterm (ε : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
    (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))

/-- The "gain" expression `X_p = caC ε · log p`. -/
noncomputable def caXterm (ε : ℝ) (p : ℕ) : ℝ :=
  Work.RHContract.Margin.caC ε * Real.log (p : ℝ)

/-- The `K₃` summand at `p`. -/
noncomputable def caK3term (ε : ℝ) (p : ℕ) : ℝ := max 0 (caYterm ε p - caXterm ε p)

lemma caK3_eq (ε : ℝ) :
    Work.RHContract.Margin.caK3 ε
      = ∑ p ∈ (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
            (fun q => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊),
          caK3term ε p := by
  simp only [Work.RHContract.Margin.caK3, caK3term, caYterm, caXterm]

/-- `⌊√ξ⌋₊ ≤ ξ`. -/
lemma sqrt_floor_le_caXi (ε : ℝ) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ ≤ Work.RHPlan.caXi ε := by
  have hξ0 : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by
    have := caXi_prime ε hξ; exact_mod_cast this.pos
  have hle : Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    nlinarith [Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
  calc ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ ≤ ⌊(Work.RHPlan.caXi ε : ℝ)⌋₊ := Nat.floor_mono hle
    _ = Work.RHPlan.caXi ε := Nat.floor_natCast _

/-- `caExpFloor ε p = ⌊log_p ξ⌋`. -/
lemma caExpFloor_eq_log (ε : ℝ) (p : ℕ) :
    Work.RHContract.Margin.caExpFloor ε p = Nat.log p (Work.RHPlan.caXi ε) := by
  unfold Work.RHContract.Margin.caExpFloor
  rw [Nat.floor_natCast]

/-- A prime `p ≤ ⌊√ξ⌋₊` has CA exponent at least `2`. -/
lemma le_caXi2_of_le_sqrt (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h2 : p ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊) :
    p ≤ Work.RHContract.Margin.caXi2 ε := by
  have hpxi : p ≤ Work.RHPlan.caXi ε := le_trans h2 (sqrt_floor_le_caXi ε hξ)
  have heS : Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
    Work.RHContract.Helper.exp_le_caExp ε hε hξ p hp hpxi
  have hξ0 : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by
    have := caXi_prime ε hξ; exact_mod_cast this.pos
  have he2 : 2 ≤ Nat.log p (Work.RHPlan.caXi ε) := by
    have hsq : p ^ 2 ≤ Work.RHPlan.caXi ε := by
      have h2' : (p : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
        have h3 : (p : ℝ) ≤ (⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ : ℝ) := by exact_mod_cast h2
        exact le_trans h3 (Nat.floor_le (Real.sqrt_nonneg _))
      have : (p : ℝ) ^ 2 ≤ (Work.RHPlan.caXi ε : ℝ) := by
        nlinarith [h2', Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
      exact_mod_cast this
    calc 2 = Nat.log p (p ^ 2) := by rw [Nat.log_pow hp.one_lt]
      _ ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.log_mono_right hsq
  have hmem : p ∈ Work.RHPlan.caSupport ε := (mem_caSupport_iff ε hε hξ).mpr ⟨hpxi, hp⟩
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨hmem, le_trans he2 heS⟩)

/-- A prime `p ∈ caSupport` with `a_p > e_p` is `≤ ξ₂`. -/
lemma le_caXi2_of_cond (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (hpxi : p ≤ Work.RHPlan.caXi ε)
    (hcond : Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊) :
    p ≤ Work.RHContract.Margin.caXi2 ε := by
  have hmem : p ∈ Work.RHPlan.caSupport ε := (mem_caSupport_iff ε hε hξ).mpr ⟨hpxi, hp⟩
  have h1 : 1 ≤ Work.RHContract.Margin.caExpFloor ε p := by
    rw [caExpFloor_eq_log]
    exact Nat.log_pos hp.one_lt hpxi
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hmem, by omega⟩)

/-- In the `a_p = e_p` regime below `√ξ`, the contribution is nonnegative. -/
lemma caContrib_ge_small_zero (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h2 : p ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊)
    (hcond : ⌊Work.RHPlan.caMu p ε⌋₊ ≤ Work.RHContract.Margin.caExpFloor ε p) :
    0 ≤ caContrib ε p := by
  obtain ⟨_, _, _, _, _, hlt6⟩ := Work.RHContract.Helper.log_taylor_bounds
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpxi : p ≤ Work.RHPlan.caXi ε := le_trans h2 (sqrt_floor_le_caXi ε hξ)
  have hfloor : Work.RHContract.Margin.caExpFloor ε p = Nat.log p (Work.RHPlan.caXi ε) :=
    caExpFloor_eq_log ε p
  have heS : Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
    Work.RHContract.Helper.exp_le_caExp ε hε hξ p hp hpxi
  have hae : ⌊Work.RHPlan.caMu p ε⌋₊ = Nat.log p (Work.RHPlan.caXi ε) := by omega
  have he2 : 2 ≤ Nat.log p (Work.RHPlan.caXi ε) := by
    have hξ0 : (0 : ℝ) < (Work.RHPlan.caXi ε : ℝ) := by
      have := caXi_prime ε hξ; exact_mod_cast this.pos
    have hsq : p ^ 2 ≤ Work.RHPlan.caXi ε := by
      have h2' : (p : ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
        have h3 : (p : ℝ) ≤ (⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ : ℝ) := by exact_mod_cast h2
        exact le_trans h3 (Nat.floor_le (Real.sqrt_nonneg _))
      have : (p : ℝ) ^ 2 ≤ (Work.RHPlan.caXi ε : ℝ) := by
        nlinarith [h2', Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
      exact_mod_cast this
    calc 2 = Nat.log p (p ^ 2) := by rw [Nat.log_pow hp.one_lt]
      _ ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.log_mono_right hsq
  have hBLE : (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) ≤ caB ε p := by
    rw [hfloor, ← hae, caB_eq (ε := ε) hp.two_le]
    rw [show -(((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) + 1))
        = -(((⌊Work.RHPlan.caMu p ε⌋₊ + 1 : ℕ) : ℝ)) by push_cast; ring]
    rw [Real.rpow_neg (le_of_lt hp0), Real.rpow_natCast]
    have hz := hlt6 ((p : ℝ) ^ (⌊Work.RHPlan.caMu p ε⌋₊ + 1))⁻¹ (by positivity)
      (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega)))
    simpa only [one_div] using hz
  have hYl : caYterm ε p ≤ (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) := by
    unfold caYterm
    have hden : (1 : ℝ) ≤ ((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)) := by
      rw [hfloor]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have h21 : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
        have hh : 1 / (p : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
        linarith
      have h3 : (3 : ℝ) ≤ (Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1 := by
        have : (2 : ℝ) ≤ (Nat.log p (Work.RHPlan.caXi ε) : ℝ) := by exact_mod_cast he2
        linarith
      nlinarith [mul_le_mul h3 h21 (by norm_num) (by linarith)]
    calc (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) /
          (((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1) * (1 - 1 / (p : ℝ)))
        ≤ ((p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1)))) / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = (p : ℝ) ^ (-(((Work.RHContract.Margin.caExpFloor ε p : ℝ) + 1))) := by rw [div_one]
  have hb : Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ) ≤ caYterm ε p := by
    have hbb := Work.RHContract.Helper.primeTailSummand_le p (Nat.log p (Work.RHPlan.caXi ε)) hp.two_le
    unfold Work.RHContract.primeTailSummand caYterm
    rw [Nat.floor_natCast]
    rw [caExpFloor_eq_log ε p]
    exact hbb
  have hzero : Work.RHContract.Margin.caC ε *
      ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ) = 0 := by
    rw [hae]; ring
  rw [caContrib, hzero]
  linarith [hBLE, hYl, hb]

/-- The master per-prime bound below `√ξ`. -/
lemma caContrib_ge_small_all (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    {p : ℕ} (hp : Nat.Prime p) (h2 : p ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊) :
    -(if Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊ then caK3term ε p else 0)
      ≤ caContrib ε p := by
  by_cases hc : Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊
  · rw [if_pos hc]
    exact caContrib_ge_small ε hε hξ hp h2
  · rw [if_neg hc, neg_zero]
    exact caContrib_ge_small_zero ε hε hξ hp h2 (by omega)

theorem ca_margin_lower (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    Work.RHContract.psiTail (Work.RHPlan.caXi ε) + Work.RHContract.Margin.caC1 ε
        + Work.RHContract.Margin.caNet2 ε - Work.RHContract.Margin.caW ε
        - Work.RHContract.Margin.caK3 ε
      ≤ Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Work.RHPlan.caNumber ε)))
          - Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
              (Work.RHPlan.caNumber ε : ℝ)) := by
  have hξp : 0 < Work.RHPlan.caXi ε := (caXi_prime ε hξ).pos
  have hS1 : ∀ p : ℕ, Nat.Prime p → p ≤ Work.RHPlan.caXi ε →
      Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊ :=
    Work.RHContract.Helper.exp_le_caExp ε hε hξ
  have hup := Work.RHContract.Helper.log_caNumber_sub_psi_bounds ε hε hξ hS1
  have hΔ0 : 0 ≤ caDelta ε := by simpa only [caDelta, caLogN, caPsi] using hup.1
  have hΔU : caDelta ε ≤ 4 * Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
    simpa only [caDelta, caLogN, caPsi] using hup.2
  have hll := loglog_step ε hε hξ hξp hΔ0 hΔU
  have hkey := key_identity ε hε hξ
  have hpt := primeTail_eq_sum_support ε hε hξ
  have hΔsum : caDelta ε = ∑ p ∈ Work.RHPlan.caSupport ε,
      (((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ)) := by
    simpa only [caDelta, caLogN, caPsi] using log_caNumber_sub_psi_eq_sum ε hε hξ
  have hprodsum : Work.RHContract.Margin.caC ε * caDelta ε
      = ∑ p ∈ Work.RHPlan.caSupport ε, Work.RHContract.Margin.caC ε *
          ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ) := by
    rw [hΔsum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hsum : Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
      - Work.RHContract.Margin.caK3 ε ≤ ∑ p ∈ Work.RHPlan.caSupport ε, caContrib ε p := by
    set S := Work.RHPlan.caSupport ε with hSdef
    have hξ2le : Work.RHContract.Margin.caXi2 ε ≤ Work.RHPlan.caXi ε := caXi2_le_caXi ε
    have hC1 : Work.RHContract.Margin.caC1 ε
        = ∑ p ∈ S.filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
            (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) := by
      rw [hSdef]
      unfold Work.RHContract.Margin.caC1
      rw [Nat.floor_natCast, ← caSupport_eq_primesLE ε hε hξ]
    have hN2 : Work.RHContract.Margin.caNet2 ε
        = ∑ p ∈ S.filter (fun q => q ≤ Work.RHContract.Margin.caXi2 ε ∧
              ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ < q),
            (Work.RHContract.Margin.caC ε * Real.log (p : ℝ) - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := by
      rw [hSdef]
      unfold Work.RHContract.Margin.caNet2
      rw [caSupport_eq_primesLE ε hε hξ]
      congr 1
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨le_trans h1 hξ2le, h2⟩, h1, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h3, h2⟩, h4⟩
    have hK3' : Work.RHContract.Margin.caK3 ε
        = ∑ p ∈ S.filter (fun q => q ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ ∧
              Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊), caK3term ε p := by
      rw [caK3_eq ε, hSdef, caSupport_eq_primesLE ε hε hξ]
      congr 1
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨le_trans h1 (sqrt_floor_le_caXi ε hξ), h2⟩, h1, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h3, h2⟩, h4⟩
    have hb1 : ∀ p ∈ S.filter (fun q => Work.RHContract.Margin.caXi2 ε < q),
        (1 / (2 * (p : ℝ) ^ 2) - 1 / (3 * (p : ℝ) ^ 3)) ≤ caContrib ε p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact caContrib_ge_large ε hε hξ (prime_of_mem_caSupport hp.1) hp.2
        ((mem_caSupport_iff ε hε hξ).mp hp.1).1
    have hb2 : ∀ p ∈ S.filter (fun q => q ≤ Work.RHContract.Margin.caXi2 ε ∧
          ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ < q),
        (Work.RHContract.Margin.caC ε * Real.log (p : ℝ) - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) ≤ caContrib ε p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hsp : Real.sqrt (Work.RHPlan.caXi ε : ℝ) < (p : ℝ) := by
        have h3 : (⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
          exact_mod_cast (by omega : ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ + 1 ≤ p)
        linarith [Nat.lt_floor_add_one (Real.sqrt (Work.RHPlan.caXi ε : ℝ))]
      exact caContrib_ge_mid ε hε hξ (prime_of_mem_caSupport hp.1) hsp hp.2.1
    have hb3 : ∀ p ∈ S.filter (fun q => q ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊),
        -(if Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊ then caK3term ε p else 0)
          ≤ caContrib ε p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact caContrib_ge_small_all ε hε hξ (prime_of_mem_caSupport hp.1) hp.2
    have e1 := Finset.sum_le_sum hb1
    have e2 := Finset.sum_le_sum hb2
    have e3 := Finset.sum_le_sum hb3
    have hS2 : S.filter (fun q => ¬ (Work.RHContract.Margin.caXi2 ε < q))
        = S.filter (fun q => q ≤ Work.RHContract.Margin.caXi2 ε) := by
      apply Finset.filter_congr
      intro q _; exact not_lt
    have hS3 : (S.filter (fun q => q ≤ Work.RHContract.Margin.caXi2 ε)).filter
          (fun q => ¬ (⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ < q))
        = S.filter (fun q => q ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro q hq
      have hq' : q ∈ Work.RHPlan.caSupport ε := by rw [hSdef] at hq; exact hq
      constructor
      · rintro ⟨_, h2⟩
        exact le_of_not_gt h2
      · intro h2
        have hle : q ≤ Work.RHContract.Margin.caXi2 ε :=
          le_caXi2_of_le_sqrt ε hε hξ (prime_of_mem_caSupport hq') h2
        exact ⟨hle, not_lt.mpr h2⟩
    have hpart1 := Finset.sum_filter_add_sum_filter_not (s := S)
      (p := fun q => Work.RHContract.Margin.caXi2 ε < q) (f := fun p => caContrib ε p)
    have hpart2 := Finset.sum_filter_add_sum_filter_not
      (s := S.filter (fun q => q ≤ Work.RHContract.Margin.caXi2 ε))
      (p := fun q => ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ < q) (f := fun p => caContrib ε p)
    rw [Finset.filter_filter] at hpart2
    rw [hS2] at hpart1
    rw [hS3] at hpart2
    have hthird : ∑ p ∈ S.filter (fun q => q ≤ ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊),
          (if Work.RHContract.Margin.caExpFloor ε p < ⌊Work.RHPlan.caMu p ε⌋₊ then caK3term ε p else 0)
        = Work.RHContract.Margin.caK3 ε := by
      rw [hK3', ← Finset.sum_filter]
      congr 1
      rw [Finset.filter_filter]
    rw [Finset.sum_neg_distrib] at e3
    linarith [e1, e2, e3, hC1, hN2, hpart1, hpart2, hthird]
  have hmain : Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
      - Work.RHContract.Margin.caK3 ε ≤
      (Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
        - Real.log (Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ))))
      + (∑ p ∈ Work.RHPlan.caSupport ε, caB ε p)
      - Work.RHContract.primeTail (Work.RHPlan.caXi ε : ℝ) := by
    have hconv : (Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
          - Real.log (Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ))))
        + (∑ p ∈ Work.RHPlan.caSupport ε, caB ε p)
        - Work.RHContract.primeTail (Work.RHPlan.caXi ε : ℝ)
        ≥ ∑ p ∈ Work.RHPlan.caSupport ε, caContrib ε p := by
      have hll' : Work.RHContract.Margin.caC ε * caDelta ε
          ≤ Real.log (Real.log (Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ)))
            - Real.log (Real.log (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ))) := hll
      rw [hprodsum] at hll'
      rw [hpt]
      have hsum_eq : ∑ p ∈ Work.RHPlan.caSupport ε, caContrib ε p
          = (∑ p ∈ Work.RHPlan.caSupport ε, Work.RHContract.Margin.caC ε *
                ((⌊Work.RHPlan.caMu p ε⌋₊ : ℝ) - (Nat.log p (Work.RHPlan.caXi ε) : ℝ)) * Real.log (p : ℝ))
            + (∑ p ∈ Work.RHPlan.caSupport ε, caB ε p)
            - ∑ p ∈ Work.RHPlan.caSupport ε,
                Work.RHContract.primeTailSummand p (Work.RHPlan.caXi ε : ℝ) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun p _ => by unfold caContrib; ring)
      rw [hsum_eq]
      linarith [hll']
    linarith [hconv, hsum]
  linarith [hkey, hmain]

end

end Work.RHContract.A
