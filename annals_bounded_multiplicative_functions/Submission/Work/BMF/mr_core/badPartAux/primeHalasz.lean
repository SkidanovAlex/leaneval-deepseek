import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.smoothing_exists
import Submission.Work.BMF.separated_row_sum
import Submission.Work.BMF.mr_core.badPartAux.dualMoment
import Submission.Work.BMF.zeta_prime_sum_twist
import Submission.Work.BMF.mr_direct.primeCounting_floor_le_div_log
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg
import Submission.Work.BMF.mr_direct.lambda_smoothed_abel_clean
import Submission.Work.BMF.mr_direct.lambda_smoothed_error_vk_pos
import Submission.Work.BMF.mr_direct.sum_mul_normSq_eq_double

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-!
# `Work.BMF.mr_direct.primePoly_halasz_vk` — Halász inequality for primes, VK form

For a short prime polynomial `Q_{j,K}(1+it) = Σ_{e^{j/K} ≤ p ≤ e^{(j+1)/K}} a_p p^{-(1+it)}`
(`mrDirect.primePoly`) and `R` one-separated points in `[-T,T]`,

  `Σ_r |Q_{j,K}(1+it_r)|² ≤ C (1 + R·exp(-c (j/K)^{1/12})) / (j/K)²`,

valid as long as `2T ≤ exp(((j/K)/2)^{21/20})` (the range of the proved
`Work.BMF.zeta_prime_sum_twist`).  This is MR Annals Lemma 11 ("Halász inequality for primes")
with the error term taken from the proved Vinogradov–Korobov prime sum instead of the
`exp(-log P/(log T)^{2/3+ε})` form, which the workspace VK (region exponent 6/7) cannot give.

Route:
1. duality (`Work.BMF.dual_moment`) with weights `log p ≥ (j/K)/2`;
2. majorise the prime window by `Λ(n) φ(n/A)`, `A = e^{j/K}`, `φ = Work.BMF.bumpFn`;
3. `Σ_n Λ(n) φ(n/A) n^{iδ} = A^{1+iδ}·Mφ(1+iδ) + E(δ)` by Abel summation plus the proved
   `Work.BMF.zeta_prime_sum_twist` (with `u = -δ`), `‖E‖ ≤ C A exp(-c (j/K)^{1/12})`;
4. main quadratic form: `Work.BMF.main_term_bound` (proved; uses `separated_row_sum`);
   error form: `≤ R·max|E|·Σ|η|²`;
5. `Σ_p ‖a p‖²/p² ≤ #{p ∈ [A, eA]}/A² ≤ C/(A log A)` (Chebyshev).
-/

namespace Work.BMF.mr_direct

open Finset MeasureTheory intervalIntegral
open scoped BigOperators

/-! ## A Chebyshev bound for `Σ 1/p²` over a short prime range -/

/-- `Σ_{⌈A⌉ ≤ p ≤ ⌊A e⌋, p prime} 1/p² ≤ C/(A log A)` for `A > 0`, `log A ≥ 4`: every summand is at
most `1/A²`, and the number of summands is bounded by Chebyshev's explicit estimate
`Work.BMF.mr_direct.primeCounting_floor_le_div_log`. -/
theorem primeInvSq_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → 4 ≤ Real.log A →
      (∑ p ∈ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) ^ 2)) ≤ C / (A * Real.log A) := by
  obtain ⟨Cπ, hCπ, hπ⟩ := Work.BMF.mr_direct.primeCounting_floor_le_div_log
  refine ⟨Cπ * Real.exp 1, by positivity, ?_⟩
  intro A hA hlogA
  have hlogApos : 0 < Real.log A := by linarith
  have hAle : Real.exp 4 ≤ A := by
    have h := Real.exp_le_exp.mpr hlogA
    rwa [Real.exp_log hA] at h
  have hAe2 : (2 : ℝ) ≤ A * Real.exp 1 := by
    have h5 : (2 : ℝ) ≤ Real.exp 4 := by
      have h6 : Real.exp (Real.log 2) ≤ Real.exp 4 :=
        Real.exp_le_exp.mpr (le_trans (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2))
          (by norm_num))
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h6
    have h7 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hlogAe : Real.log (A * Real.exp 1) = Real.log A + 1 := by
    rw [Real.log_mul hA.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hcard : (((Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime).card : ℝ)
      ≤ Cπ * (A * Real.exp 1) / Real.log (A * Real.exp 1) := by
    have h1 : (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime
        ⊆ (Finset.range (⌊A * Real.exp 1⌋₊ + 1)).filter Nat.Prime := by
      intro n hn
      obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hmem).2), hprime⟩
    have h2 : ((Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime).card
        ≤ (⌊A * Real.exp 1⌋₊).primeCounting := by
      rw [← Nat.primesLE_card_eq_primeCounting (⌊A * Real.exp 1⌋₊)]
      exact Finset.card_le_card h1
    exact le_trans (by exact_mod_cast h2) (hπ (A * Real.exp 1) hAe2)
  calc (∑ p ∈ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) ^ 2))
      ≤ ∑ _p ∈ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime, (1 : ℝ) / A ^ 2 := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hp
        have hpge : A ≤ (p : ℝ) := by
          have h1 : (⌈A⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hmem).1
          exact le_trans (Nat.le_ceil A) h1
        have hp2 : 0 < (p : ℝ) := lt_of_lt_of_le hA hpge
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = (((Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime).card : ℝ) * (1 / A ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cπ * (A * Real.exp 1) / Real.log (A * Real.exp 1)) * (1 / A ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ Cπ * Real.exp 1 / (A * Real.log A) := by
        have heq : (Cπ * (A * Real.exp 1) / Real.log (A * Real.exp 1)) * (1 / A ^ 2)
            = Cπ * Real.exp 1 / (A * (Real.log A + 1)) := by
          rw [hlogAe]
          field_simp
        rw [heq]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hCπ.le, Real.exp_pos 1, hA, hlogApos]

/-! ## Elementary conjugation of a pure phase -/

private lemma conj_cpow_neg_I (n : ℕ) (u : ℝ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-(Complex.I * (u : ℂ)))) = (n : ℂ) ^ (Complex.I * (u : ℂ)) := by
  have hexp : (starRingEnd ℂ) (-(Complex.I * (u : ℂ))) = Complex.I * (u : ℂ) := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [← Complex.ofReal_natCast,
    Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (Nat.cast_nonneg n), Complex.ofReal_natCast,
    hexp]

private lemma norm_starRingEnd (z : ℂ) : ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
  simp

/-! ## The target -/

theorem primePoly_halasz_vk :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (K : ℝ) (j : ℕ) (T : ℝ) (R : ℕ) (t : Fin R → ℝ) (a : ℕ → ℂ),
        2 ≤ K → 4 ≤ (j : ℝ) / K → 3 ≤ T →
        2 * T ≤ Real.exp (((j : ℝ) / K / 2) ^ (21 / 20 : ℝ)) →
        (∀ p, ‖a p‖ ≤ 1) →
        (∀ i i' : Fin R, i ≠ i' → 1 ≤ |t i - t i'|) →
        (∀ i, t i ∈ Set.Icc (-T) T) →
        (∑ r : Fin R, ‖Work.BMF.mrDirect.primePoly a K j (t r)‖ ^ 2)
          ≤ C * (1 + (R : ℝ) * Real.exp (-c * ((j : ℝ) / K) ^ (1 / 12 : ℝ)))
              / ((j : ℝ) / K) ^ 2 := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hErr⟩ := lambda_smoothed_error_vk_pos
  obtain ⟨Cπ, hCπ, hπ⟩ := primeInvSq_sum_le
  obtain ⟨Crow, hCrow, hrow⟩ := Work.BMF.separated_row_sum
  set Cφ : ℝ := 64 * (∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv Work.BMF.bumpFn) y : ℝ) : ℂ))‖) + 1
    with hCφdef
  have hCφpos : 0 < Cφ := by
    rw [hCφdef]
    have hnn : 0 ≤ ∫ y in (1 / 8 : ℝ)..8, ‖(((deriv (deriv Work.BMF.bumpFn) y : ℝ) : ℂ))‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
    linarith
  have hdecay : ∀ τ : ℝ,
      ‖∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (τ : ℂ)) * ((Work.BMF.bumpFn y) : ℂ)‖
        ≤ Cφ / (1 + τ ^ 2) := by
    intro τ
    rw [hCφdef, Work.BMF.integral_shift τ, Work.BMF.integral_ibp τ]
    exact Work.BMF.integral_norm_bound τ
  refine ⟨c₁, 2 * Cπ * (Cφ * Crow + C₁), hc₁, by positivity, ?_⟩
  intro K j T R t a hK hj hT hTexp ha hsep hIcc
  have hKpos : 0 < K := by linarith
  set L : ℝ := (j : ℝ) / K with hLdef
  have hL4 : 4 ≤ L := hj
  have hLpos : 0 < L := by linarith
  set A : ℝ := Real.exp L with hAdef
  have hApos : 0 < A := Real.exp_pos L
  have hlogA : Real.log A = L := Real.log_exp L
  have hAexp : Real.exp ((j : ℝ) / K) = A := by rw [← hLdef, ← hAdef]
  have hAexp1 : Real.exp (((j : ℝ) + 1) / K) = A * Real.exp (1 / K) := by
    have hsp : ((j : ℝ) + 1) / K = (j : ℝ) / K + 1 / K := by ring
    rw [hsp, Real.exp_add, hAexp]
  have hexpK2 : Real.exp (1 / K) ≤ 2 := by
    have h1 : 1 / K ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 2)]; linarith
    have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    calc Real.exp (1 / K) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (le_trans h1 h2)
      _ = 2 := Real.exp_log (by norm_num)
  have hexpKe : Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by
    rw [div_le_one hKpos]; linarith)
  set M : ℕ := ⌈4 * A⌉₊ with hMdef
  have hMge : 4 * A ≤ (M : ℝ) := by rw [hMdef]; exact Nat.le_ceil _
  set N : Finset ℕ :=
    ((Finset.Icc ⌈Real.exp ((j : ℝ) / K)⌉₊ ⌊Real.exp (((j : ℝ) + 1) / K)⌋₊).filter Nat.Prime)
    with hNdef
  -- the prime polynomial, rewritten over `N`
  have hpoly : ∀ r : Fin R, Work.BMF.mrDirect.primePoly a K j (t r)
      = ∑ n ∈ N, ((n : ℂ)⁻¹ * a n) * (n : ℂ) ^ (-(Complex.I * ((t r : ℝ) : ℂ))) := by
    intro r
    unfold Work.BMF.mrDirect.primePoly
    rw [← hNdef]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨_, hprime⟩ := Finset.mem_filter.mp hp
    have hp0 : (p : ℂ) ≠ 0 := by
      have : p ≠ 0 := hprime.ne_zero
      exact_mod_cast this
    rw [show -(1 + Complex.I * ((t r : ℝ) : ℂ)) = -1 + -(Complex.I * ((t r : ℝ) : ℂ)) by ring,
      Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
    ring
  -- membership facts about `N`
  have hNhi : ∀ n ∈ N, (n : ℝ) ≤ Real.exp (((j : ℝ) + 1) / K) := by
    intro n hn
    rw [hNdef] at hn
    obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hhi⟩ := Finset.mem_Icc.mp hmem
    exact le_trans (by exact_mod_cast hhi) (Nat.floor_le (Real.exp_nonneg _))
  have hNhiA : ∀ n ∈ N, (n : ℝ) ≤ A * Real.exp 1 := by
    intro n hn
    have h1 : Real.exp (((j : ℝ) + 1) / K) ≤ A * Real.exp 1 := by
      rw [hAexp1]; exact mul_le_mul_of_nonneg_left hexpKe hApos.le
    exact le_trans (hNhi n hn) h1
  have hNle : ∀ n ∈ N, n ≤ M := by
    intro n hn
    have h1 : (n : ℝ) ≤ 4 * A := by
      have h2 : Real.exp (((j : ℝ) + 1) / K) ≤ 4 * A := by
        rw [hAexp1]
        have h3 := mul_le_mul_of_nonneg_left hexpK2 hApos.le
        linarith
      linarith [hNhi n hn]
    exact_mod_cast (le_trans h1 hMge)
  have hNge : ∀ n ∈ N, 1 ≤ n := by
    intro n hn
    rw [hNdef] at hn
    obtain ⟨_, hprime⟩ := Finset.mem_filter.mp hn
    exact le_trans (by norm_num : 1 ≤ 2) hprime.two_le
  have hNlo : ∀ n ∈ N, A ≤ (n : ℝ) := by
    intro n hn
    rw [hNdef] at hn
    obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, _⟩ := Finset.mem_Icc.mp hmem
    have h1 : (⌈Real.exp ((j : ℝ) / K)⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    have h2 : A ≤ (⌈Real.exp ((j : ℝ) / K)⌉₊ : ℝ) := by rw [← hAexp]; exact Nat.le_ceil _
    linarith
  have hNlog : ∀ n ∈ N, L / 2 ≤ Real.log n := by
    intro n hn
    have h1 : Real.log A ≤ Real.log n := Real.log_le_log hApos (hNlo n hn)
    rw [hlogA] at h1
    linarith
  -- the coefficients of the smoothed `Λ`-sum
  set cw : ℕ → ℂ :=
    fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((Work.BMF.bumpFn (n / A)) : ℂ)
    with hcwdef
  set X : Fin R → ℕ → ℂ :=
    fun r n => (n : ℂ) ^ (-(Complex.I * ((t r : ℝ) : ℂ))) with hXdef
  set E : ℝ := Real.exp (-c₁ * L ^ (1 / 12 : ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  set D : ℝ := A * (Cφ * Crow + C₁ * (R : ℝ) * E) with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  -- the dual quadratic-form hypothesis
  have hQ : ∀ b : Fin R → ℂ,
      ∑ n ∈ N, Real.log n * ‖∑ i, b i * (starRingEnd ℂ) (X i n)‖ ^ 2
        ≤ D * ∑ i, ‖b i‖ ^ 2 := by
    intro b
    have hswap : (∑ n ∈ N, Real.log n * ‖∑ i, b i * (starRingEnd ℂ) (X i n)‖ ^ 2)
        = ∑ n ∈ N, Real.log n * ‖∑ i, b i * (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      have hh : (∑ i, b i * (starRingEnd ℂ) (X i n))
          = ∑ i, b i * (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hx : X i n = (n : ℂ) ^ (-(Complex.I * ((t i : ℝ) : ℂ))) := by
          simp only [hXdef]
        rw [hx, conj_cpow_neg_I n (t i)]
      rw [hh]
    rw [hswap]
    set nrm : ℕ → ℝ :=
      fun n => ‖∑ i, b i * (n : ℂ) ^ (Complex.I * ((t i : ℝ) : ℂ))‖ ^ 2 with hnrmdef
    -- majorisation by the `Λ`-smoothed sum
    have hmaj : (∑ n ∈ N, Real.log n * nrm n)
        ≤ ∑ n ∈ Finset.Icc 1 M,
            (ArithmeticFunction.vonMangoldt n : ℝ) * (Work.BMF.bumpFn (n / A)) * nrm n := by
      have heq : (∑ n ∈ N, Real.log n * nrm n)
          = ∑ n ∈ N,
              (ArithmeticFunction.vonMangoldt n : ℝ) * (Work.BMF.bumpFn (n / A)) * nrm n := by
        refine Finset.sum_congr rfl (fun n hn' => ?_)
        have hn1 : 1 ≤ n := hNge n hn'
        have hLam : ArithmeticFunction.vonMangoldt n = Real.log n := by
          rw [hNdef] at hn'
          exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn').2
        have hphi : Work.BMF.bumpFn (n / A) = 1 := by
          apply Work.BMF.bumpFn_eq_one
          constructor
          · rw [le_div_iff₀ hApos]; linarith [hNlo n (by rw [hNdef]; exact hn')]
          · rw [div_le_iff₀ hApos]
            have h2 : Real.exp (((j : ℝ) + 1) / K) ≤ 2 * A := by
              rw [hAexp1]
              have h3 := mul_le_mul_of_nonneg_left hexpK2 hApos.le
              linarith
            linarith [hNhi n (by rw [hNdef]; exact hn')]
        rw [hLam, hphi, mul_one]
      rw [heq]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨hNge n hn, hNle n hn⟩
      · intro n _ _
        exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Work.BMF.bumpFn_nonneg _))
          (by positivity)
    -- the double-sum expansion
    have hident := sum_mul_normSq_eq_double cw b t (Finset.Icc 1 M)
      (fun n hn => (Finset.mem_Icc.mp hn).1)
    set Sij : Fin R → Fin R → ℂ :=
      fun i j => ∑ n ∈ Finset.Icc 1 M, cw n * (n : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ))
      with hSijdef
    have hreal : (∑ n ∈ Finset.Icc 1 M,
          (ArithmeticFunction.vonMangoldt n : ℝ) * (Work.BMF.bumpFn (n / A)) * nrm n)
        = (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Sij i j).re := by
      have hcast : ((∑ n ∈ Finset.Icc 1 M,
            (ArithmeticFunction.vonMangoldt n : ℝ) * (Work.BMF.bumpFn (n / A)) * nrm n : ℝ) : ℂ)
          = ∑ n ∈ Finset.Icc 1 M, cw n * ((nrm n : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        simp only [hcwdef]
        push_cast
        ring
      have hmid : (∑ n ∈ Finset.Icc 1 M, cw n * ((nrm n : ℝ) : ℂ))
          = ∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Sij i j := by
        simpa only [hnrmdef, hSijdef] using hident
      rw [← hmid, ← hcast, Complex.ofReal_re]
    -- the pointwise split into main term + error and the error bound
    set Mterm : Fin R → Fin R → ℂ :=
      fun i j => (A : ℂ) ^ (1 + Complex.I * (((t i - t j : ℝ)) : ℂ)) *
        (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (((t i - t j : ℝ)) : ℂ)) *
          ((Work.BMF.bumpFn y) : ℂ)) with hMtermdef
    set Eterm : ℝ → ℂ :=
      fun δ => -(∫ τ in (0 : ℝ)..(M : ℝ),
        (((deriv Work.BMF.bumpFn (τ / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((∑ n ∈ Finset.Icc 1 ⌊τ⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)))
            - (τ : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))) with hEtermdef
    have habel : ∀ δ : ℝ,
        (∑ n ∈ Finset.Icc 1 M, cw n * (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          = (A : ℂ) ^ (1 + Complex.I * (δ : ℂ)) *
              (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (δ : ℂ)) *
                ((Work.BMF.bumpFn y) : ℂ))
            + Eterm δ := by
      intro δ
      have h0 := lambda_smoothed_abel_clean A δ hApos (by rw [hlogA]; exact hL4)
      rw [← hMdef] at h0
      have hLsum : (∑ n ∈ Finset.Icc 1 M, cw n * (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          = ∑ n ∈ Finset.Icc 1 M, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)) * ((Work.BMF.bumpFn (n / A)) : ℂ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        simp only [hcwdef]
        ring
      rw [hLsum, h0]
      simp only [hEtermdef]
      ring
    have hEbound : ∀ δ : ℝ, |δ| ≤ 2 * T → ‖Eterm δ‖ ≤ C₁ * A * E := by
      intro δ hδ
      have h0 := hErr A T δ hApos (by rw [hlogA]; exact hL4) hT hδ (by rw [hlogA]; exact hTexp)
      rw [← hMdef, hlogA] at h0
      simp only [hEtermdef, hEdef, norm_neg]
      exact h0
    have hSij : ∀ i j : Fin R, Sij i j = Mterm i j + Eterm (t i - t j) := fun i j => by
      simpa only [hSijdef, hMtermdef] using habel (t i - t j)
    have hd_le : ∀ i j : Fin R, |t i - t j| ≤ 2 * T := by
      intro i j
      obtain ⟨hi1, hi2⟩ := hIcc i
      obtain ⟨hj1, hj2⟩ := hIcc j
      rw [abs_le]
      constructor <;> linarith
    -- the main term
    have hMbound : ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Mterm i j‖
        ≤ Cφ * Crow * A * ∑ i, ‖b i‖ ^ 2 := by
      have h0 := Work.BMF.main_term_bound (R := R) Work.BMF.bumpFn (Cφ := Cφ) (Crow := Crow)
        (P := A) hCφpos hApos hdecay t (hrow R t hsep) b
      simpa only [hMtermdef, mul_assoc] using h0
    -- the error term
    have hEbound2 : ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)‖
        ≤ C₁ * A * E * (R : ℝ) * ∑ i, ‖b i‖ ^ 2 := by
      have h1 : ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)‖
          ≤ ∑ i, ∑ j, ‖b i‖ * ‖b j‖ * (C₁ * A * E) := by
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum (fun j _ => ?_)
        have heq : ‖b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)‖
            = ‖b i‖ * ‖b j‖ * ‖Eterm (t i - t j)‖ := by
          rw [norm_mul, norm_mul, norm_starRingEnd]
        rw [heq]
        exact mul_le_mul_of_nonneg_left (hEbound _ (hd_le i j)) (by positivity)
      have h2 : (∑ i, ∑ j, ‖b i‖ * ‖b j‖ * (C₁ * A * E))
          = (C₁ * A * E) * (∑ i, ‖b i‖) ^ 2 := by
        have h1 : (∑ i, ∑ j, ‖b i‖ * ‖b j‖ * (C₁ * A * E))
            = (∑ i, ∑ j, ‖b i‖ * ‖b j‖) * (C₁ * A * E) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
        rw [h1, ← Finset.sum_mul_sum, sq]
        ring
      have h3 : (∑ i : Fin R, ‖b i‖) ^ 2 ≤ (R : ℝ) * ∑ i, ‖b i‖ ^ 2 := by
        have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin R => ‖b i‖)
        rw [Finset.card_univ, Fintype.card_fin] at h0
        simpa using h0
      calc ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)‖
          ≤ (C₁ * A * E) * (∑ i, ‖b i‖) ^ 2 := le_trans h1 (le_of_eq h2)
        _ ≤ (C₁ * A * E) * ((R : ℝ) * ∑ i, ‖b i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = C₁ * A * E * (R : ℝ) * ∑ i, ‖b i‖ ^ 2 := by ring
    -- assemble
    have hsplit : (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Sij i j)
        = (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Mterm i j)
          + (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hSij i j, mul_add]
    have hbd : (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Sij i j).re
        ≤ D * ∑ i, ‖b i‖ ^ 2 := by
      rw [hsplit]
      calc ((∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Mterm i j)
              + (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j))).re
          ≤ ‖(∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Mterm i j)
              + (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j))‖ :=
            Complex.re_le_norm _
        _ ≤ ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Mterm i j‖
              + ‖∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Eterm (t i - t j)‖ := norm_add_le _ _
        _ ≤ Cφ * Crow * A * ∑ i, ‖b i‖ ^ 2 + C₁ * A * E * (R : ℝ) * ∑ i, ‖b i‖ ^ 2 :=
            add_le_add hMbound hEbound2
        _ = D * ∑ i, ‖b i‖ ^ 2 := by rw [hDdef]; ring
    calc (∑ n ∈ N, Real.log n * nrm n)
        ≤ ∑ n ∈ Finset.Icc 1 M,
            (ArithmeticFunction.vonMangoldt n : ℝ) * (Work.BMF.bumpFn (n / A)) * nrm n := hmaj
      _ = (∑ i, ∑ j, b i * (starRingEnd ℂ) (b j) * Sij i j).re := hreal
      _ ≤ D * ∑ i, ‖b i‖ ^ 2 := hbd
  -- duality
  have hdual := Work.BMF.dual_moment N X (fun n => Real.log n) (c := L / 2) (D := D)
    (by linarith) hD0 hNlog hQ (fun n => (n : ℂ)⁻¹ * a n)
  -- the left-hand side is the sum we want
  have hLHS : (∑ r : Fin R, ‖Work.BMF.mrDirect.primePoly a K j (t r)‖ ^ 2)
      = ∑ r : Fin R, ‖∑ n ∈ N, ((n : ℂ)⁻¹ * a n) * X r n‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [hpoly r]
  -- the right-hand side: `Σ_p ‖a p‖²/p² ≤ Cπ/(A L)`
  have hsum2 : (∑ n ∈ N, ‖((n : ℂ)⁻¹ * a n)‖ ^ 2) ≤ Cπ / (A * L) := by
    have h1 : ∀ n ∈ N, ‖((n : ℂ)⁻¹ * a n)‖ ^ 2 ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
      intro n hn
      have hn1 : 1 ≤ n := hNge n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      have ha' : ‖a n‖ ≤ 1 := ha n
      have hs : ‖a n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (a n), ha']
      calc ((n : ℝ)⁻¹ * ‖a n‖) ^ 2 = ((n : ℝ)⁻¹) ^ 2 * ‖a n‖ ^ 2 := by ring
        _ ≤ ((n : ℝ)⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 1 / (n : ℝ) ^ 2 := by rw [mul_one, inv_pow, one_div]
    have h2 : (∑ n ∈ N, (1 : ℝ) / (n : ℝ) ^ 2)
        ≤ ∑ p ∈ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 := by
      have hsub : N ⊆ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime := by
        intro n hn
        rw [hNdef] at hn
        obtain ⟨hmem, hprime⟩ := Finset.mem_filter.mp hn
        obtain ⟨hlo, _⟩ := Finset.mem_Icc.mp hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hprime⟩
        · have h1 : A ≤ (⌈Real.exp ((j : ℝ) / K)⌉₊ : ℝ) := by
            rw [← hAexp]; exact Nat.le_ceil _
          have h2 : (⌈Real.exp ((j : ℝ) / K)⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
          linarith
        · exact Nat.le_floor (hNhiA n (by rw [hNdef]; exact hn))
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    calc (∑ n ∈ N, ‖((n : ℂ)⁻¹ * a n)‖ ^ 2)
        ≤ ∑ n ∈ N, (1 : ℝ) / (n : ℝ) ^ 2 := Finset.sum_le_sum h1
      _ ≤ ∑ p ∈ (Finset.Icc ⌈A⌉₊ ⌊A * Real.exp 1⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 := h2
      _ ≤ Cπ / (A * L) := by
          have h0 := hπ A hApos (by rw [hlogA]; exact hL4)
          simpa only [hlogA] using h0
  -- the arithmetic
  have hstep : D / (L / 2) * (Cπ / (A * L))
      ≤ 2 * Cπ * (Cφ * Crow + C₁) * (1 + (R : ℝ) * E) / L ^ 2 := by
    have hnum : Cφ * Crow + C₁ * (R : ℝ) * E
        ≤ (Cφ * Crow + C₁) * (1 + (R : ℝ) * E) := by
      have h1 : 0 ≤ Cφ * Crow := by positivity
      have h2 : 0 ≤ (R : ℝ) * E := by positivity
      have h3 : 0 ≤ C₁ := hC₁.le
      nlinarith [mul_nonneg h1 h2, mul_nonneg h3 h2]
    have heq : D / (L / 2) * (Cπ / (A * L))
        = 2 * Cπ * (Cφ * Crow + C₁ * (R : ℝ) * E) / L ^ 2 := by
      have hAne : A ≠ 0 := ne_of_gt hApos
      have hLne : L ≠ 0 := ne_of_gt hLpos
      rw [hDdef]
      field_simp
    have hC2 : (0 : ℝ) ≤ 2 * Cπ * L ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_right hnum hC2
    rw [heq, div_le_div_iff₀ (by positivity : (0:ℝ) < L ^ 2) (by positivity : (0:ℝ) < L ^ 2)]
    nlinarith [h3]
  have hfinal : (∑ r : Fin R, ‖Work.BMF.mrDirect.primePoly a K j (t r)‖ ^ 2)
      ≤ 2 * Cπ * (Cφ * Crow + C₁) * (1 + (R : ℝ) * E) / L ^ 2 := by
    calc (∑ r : Fin R, ‖Work.BMF.mrDirect.primePoly a K j (t r)‖ ^ 2)
        = ∑ r : Fin R, ‖∑ n ∈ N, ((n : ℂ)⁻¹ * a n) * X r n‖ ^ 2 := hLHS
      _ ≤ D / (L / 2) * ∑ n ∈ N, ‖((n : ℂ)⁻¹ * a n)‖ ^ 2 := hdual
      _ ≤ D / (L / 2) * (Cπ / (A * L)) := by
          apply mul_le_mul_of_nonneg_left hsum2
          positivity
      _ ≤ 2 * Cπ * (Cφ * Crow + C₁) * (1 + (R : ℝ) * E) / L ^ 2 := hstep
  rw [hEdef, hLdef] at hfinal
  exact hfinal

end Work.BMF.mr_direct
