import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.NumberTheory.DivisorBound.sum_sqfree_tau_div_mul_totient_le_const
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

namespace Commons.NumberTheory.DivisorBound

open Finset
open scoped BigOperators

noncomputable section

/-- `1/φ(d)` if `d` is squarefree, `0` otherwise (as a real function). -/
private def sfInvPhi (d : ℕ) : ℝ := if Squarefree d then (Nat.totient d : ℝ)⁻¹ else 0

private lemma sfInvPhi_one : sfInvPhi 1 = 1 := by
  simp only [sfInvPhi]
  rw [if_pos squarefree_one, Nat.totient_one, Nat.cast_one, inv_one]

private lemma sfInvPhi_mul (a b : ℕ) (h : Nat.Coprime a b) :
    sfInvPhi (a * b) = sfInvPhi a * sfInvPhi b := by
  by_cases hab : Squarefree (a * b)
  · obtain ⟨ha, hb⟩ := (Nat.squarefree_mul h).mp hab
    have hφ : (Nat.totient (a * b) : ℝ) = (Nat.totient a : ℝ) * (Nat.totient b : ℝ) := by
      rw [Nat.totient_mul h, Nat.cast_mul]
    simp only [sfInvPhi]
    rw [if_pos hab, if_pos ha, if_pos hb, hφ, mul_inv]
  · have hns : ¬ (Squarefree a ∧ Squarefree b) := fun hh => hab ((Nat.squarefree_mul h).mpr hh)
    rcases not_and_or.mp hns with ha | hb
    · simp only [sfInvPhi]
      rw [if_neg hab, if_neg ha]
      ring
    · simp only [sfInvPhi]
      rw [if_neg hab, if_neg hb]
      ring

private lemma sfInvPhi_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    sfInvPhi (p ^ k) = 0 := by
  have hns : ¬ Squarefree (p ^ k) := by
    intro hsq
    have hu : IsUnit p := hsq p (by simpa [pow_two] using (pow_dvd_pow p hk))
    exact hp.ne_one (Nat.isUnit_iff.mp hu)
  simp only [sfInvPhi]
  rw [if_neg hns]

/-- **Euler product identity**: for `d ≥ 1`, the product `∏_{p | d} p/(p-1)` equals the
sum of `1/φ(e)` over the squarefree divisors `e` of `d`. -/
theorem prod_primeFactors_div_sub_one_eq_sum_sqfree_inv_totient :
    ∀ d : ℕ, 0 < d →
      (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
        = ∑ e ∈ (Nat.divisors d).filter Squarefree, 1 / (Nat.totient e : ℝ) := by
  intro d hd
  have hdne : d ≠ 0 := hd.ne'
  have hmain := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    sfInvPhi d hdne sfInvPhi_one sfInvPhi_mul sfInvPhi_prime_pow
  have h1 : (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) =
      ∏ p ∈ d.primeFactors, (1 + sfInvPhi p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hsf : sfInvPhi p = 1 / (Nat.totient p : ℝ) := by
      simp only [sfInvPhi]
      rw [if_pos hpp.squarefree, one_div]
    rw [hsf, Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hne : ((p : ℝ) - 1) ≠ 0 := by linarith
    have key : (1 : ℝ) + 1 / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) := by
      rw [eq_div_iff hne, add_mul, one_mul, div_mul_cancel₀ (1 : ℝ) hne]
      ring
    exact key.symm
  have h2 : (∑ e ∈ d.divisors, sfInvPhi e) =
      ∑ e ∈ (Nat.divisors d).filter Squarefree, 1 / (Nat.totient e : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    simp only [sfInvPhi]
    by_cases hsq : Squarefree e
    · rw [if_pos hsq, if_pos hsq, one_div]
    · rw [if_neg hsq, if_neg hsq]
  rw [h1, hmain, h2]

/-- Weight `τ(e)/(e·φ(e))`. -/
private def W (e : ℕ) : ℝ := ((Nat.divisors e).card : ℝ) / ((e : ℝ) * (Nat.totient e : ℝ))

/-- Weight `τ(f)/f`. -/
private def H (f : ℕ) : ℝ := ((Nat.divisors f).card : ℝ) / (f : ℝ)

/-- Pointwise bound: `(τ(d)/d)·∏_{p|d} p/(p-1)` is at most the Dirichlet convolution
of the squarefree weight `W` with the divisor-count weight `H`. -/
private lemma term_le_conv (d : ℕ) (hd : 1 ≤ d) :
    ((Nat.divisors d).card : ℝ) / (d : ℝ)
        * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
      ≤ ∑ e ∈ (Nat.divisors d).filter Squarefree, W e * H (d / e) := by
  classical
  have hdpos : 0 < d := by omega
  rw [prod_primeFactors_div_sub_one_eq_sum_sqfree_inv_totient d hdpos, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  rw [Finset.mem_filter, Nat.mem_divisors] at he
  obtain ⟨⟨hedvd, _⟩, _hsq⟩ := he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hdpos
  have hfpos : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hdpos hedvd) hepos
  have hmul : e * (d / e) = d := Nat.mul_div_cancel' hedvd
  have hcard : ((Nat.divisors d).card : ℝ)
      ≤ ((Nat.divisors e).card : ℝ) * ((Nat.divisors (d / e)).card : ℝ) := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le e (d / e)
    rw [hmul] at h
    exact_mod_cast h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hcastd : (d : ℝ) = (e : ℝ) * ((d / e : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, hmul]
  have hstep : ((Nat.divisors d).card : ℝ) / (d : ℝ) * (1 / (Nat.totient e : ℝ))
      ≤ (((Nat.divisors e).card : ℝ) * ((Nat.divisors (d / e)).card : ℝ)) / (d : ℝ)
          * (1 / (Nat.totient e : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hcard hdR.le
  have hfin : (((Nat.divisors e).card : ℝ) * ((Nat.divisors (d / e)).card : ℝ)) / (d : ℝ)
        * (1 / (Nat.totient e : ℝ))
      = W e * H (d / e) := by
    rw [hcastd, W, H]
    ring_nf
  linarith [hstep, hfin.le, hfin.ge]

/-- **Reindexing (Dirichlet convolution bound)**: for nonnegative `w` and `h`, the double
sum `∑_{d ≤ V} ∑_{e | d, e squarefree} w e · h(d/e)` is at most
`(∑_{e ≤ V, squarefree} w e)·(∑_{f ≤ V} h f)`. -/
theorem sum_sqfree_dvd_reindex (w h : ℕ → ℝ)
    (hw : ∀ e, Squarefree e → 0 ≤ w e) (hh : ∀ f, 0 ≤ h f) (V : ℕ) :
    (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ (Nat.divisors d).filter Squarefree, w e * h (d / e))
      ≤ (∑ e ∈ (Finset.Icc 1 V).filter Squarefree, w e) * (∑ f ∈ Finset.Icc 1 V, h f) := by
  classical
  have step1 : ∀ d ∈ Finset.Icc 1 V,
      (∑ e ∈ (Nat.divisors d).filter Squarefree, w e * h (d / e))
        = ∑ e ∈ (Finset.Icc 1 V).filter Squarefree, (if e ∣ d then w e * h (d / e) else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdV : d ≤ V := (Finset.mem_Icc.mp hd).2
    have hset : ((Finset.Icc 1 V).filter Squarefree).filter (fun e => e ∣ d)
        = (Nat.divisors d).filter Squarefree := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨_h1, _hle⟩, hsq⟩, hdvd⟩
        exact ⟨⟨hdvd, by omega⟩, hsq⟩
      · rintro ⟨⟨hdvd, _⟩, hsq⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hdV⟩, hsq⟩, hdvd⟩
    rw [← hset, Finset.sum_filter]
  calc ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ (Nat.divisors d).filter Squarefree, w e * h (d / e)
      = ∑ d ∈ Finset.Icc 1 V,
          ∑ e ∈ (Finset.Icc 1 V).filter Squarefree, (if e ∣ d then w e * h (d / e) else 0) :=
        Finset.sum_congr rfl step1
    _ = ∑ e ∈ (Finset.Icc 1 V).filter Squarefree,
          ∑ d ∈ Finset.Icc 1 V, (if e ∣ d then w e * h (d / e) else 0) := Finset.sum_comm
    _ = ∑ e ∈ (Finset.Icc 1 V).filter Squarefree, w e * ∑ f ∈ Finset.Icc 1 (V / e), h f := by
        apply Finset.sum_congr rfl
        intro e he
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
        rw [← Finset.sum_filter]
        rw [Commons.NumberTheory.DivisorSum.sum_Icc_filter_dvd V e he1 (fun n => w e * h (n / e))]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        rw [Nat.mul_div_cancel_left f (by omega : 0 < e)]
    _ ≤ (∑ e ∈ (Finset.Icc 1 V).filter Squarefree, w e) * (∑ f ∈ Finset.Icc 1 V, h f) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro e he
        have hwe : 0 ≤ w e := hw e (Finset.mem_filter.mp he).2
        apply mul_le_mul_of_nonneg_left _ hwe
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hf).1,
            le_trans (Finset.mem_Icc.mp hf).2 (Nat.div_le_self V e)⟩
        · intro f _ _; exact hh f

/-- The weighted divisor sum `∑_{d ≤ V} (τ(d)/d)·∏_{p|d} p/(p-1)` is `O(∑_{f≤V} τ(f)/f)`. -/
private lemma sum_le_const_mul_tau_sum (Cw : ℝ)
    (hw : ∀ V : ℕ, (∑ e ∈ (Finset.Icc 1 V).filter Squarefree, W e) ≤ Cw) :
    ∀ V : ℕ,
      (∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
          * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)))
        ≤ Cw * (∑ f ∈ Finset.Icc 1 V, H f) := by
  intro V
  have hWnn : ∀ e, Squarefree e → 0 ≤ W e := by
    intro e _; exact div_nonneg (by positivity) (by positivity)
  have hHnn : ∀ f, 0 ≤ H f := by
    intro f; exact div_nonneg (by positivity) (by positivity)
  have hterm : ∀ d ∈ Finset.Icc 1 V,
      ((Nat.divisors d).card : ℝ) / (d : ℝ)
          * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
        ≤ ∑ e ∈ (Nat.divisors d).filter Squarefree, W e * H (d / e) := by
    intro d hd
    exact term_le_conv d (Finset.mem_Icc.mp hd).1
  have hre := sum_sqfree_dvd_reindex W H hWnn hHnn V
  have hWsum : (∑ e ∈ (Finset.Icc 1 V).filter Squarefree, W e) ≤ Cw := hw V
  have hHsum : 0 ≤ ∑ f ∈ Finset.Icc 1 V, H f := Finset.sum_nonneg (fun f _ => hHnn f)
  calc (∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
          * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)))
      ≤ ∑ d ∈ Finset.Icc 1 V, ∑ e ∈ (Nat.divisors d).filter Squarefree, W e * H (d / e) :=
        Finset.sum_le_sum hterm
    _ ≤ (∑ e ∈ (Finset.Icc 1 V).filter Squarefree, W e) * (∑ f ∈ Finset.Icc 1 V, H f) := hre
    _ ≤ Cw * (∑ f ∈ Finset.Icc 1 V, H f) :=
        mul_le_mul_of_nonneg_right hWsum hHsum

theorem sum_tau_prod_prime_div_le_logsq :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ,
      ∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
        * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
        ≤ C * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
  obtain ⟨Cw, hCwpos, hCw⟩ := sum_sqfree_tau_div_mul_totient_le_const
  obtain ⟨Ct, hCtpos, hCt⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit 1
  refine ⟨max (2 * Cw * Ct) (max (2 * Cw) 1), ?_, ?_⟩
  · have hpos : 0 < 2 * Cw * Ct := by positivity
    exact lt_of_lt_of_le hpos (le_max_left _ _)
  · intro V
    have hCmax_ge_2Cw : 2 * Cw ≤ max (2 * Cw * Ct) (max (2 * Cw) 1) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hCmax_ge_1 : (1 : ℝ) ≤ max (2 * Cw * Ct) (max (2 * Cw) 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hCmax_nonneg : (0 : ℝ) ≤ max (2 * Cw * Ct) (max (2 * Cw) 1) :=
      le_trans zero_le_one hCmax_ge_1
    have hbase := sum_le_const_mul_tau_sum Cw hCw
    by_cases hV : 2 ≤ V
    · -- main case
      have hU : (∑ f ∈ Finset.Icc 1 V, H f) ≤ Ct * (Real.log (V : ℝ)) ^ 2 := by
        have h := hCt V hV
        have hp : (Real.log (V : ℝ)) ^ ((2 : ℝ) ^ (1 : ℕ)) = (Real.log (V : ℝ)) ^ 2 := by
          rw [show ((2 : ℝ) ^ (1 : ℕ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [hp] at h
        simpa only [H, pow_one] using h
      have hlogVnn : 0 ≤ Real.log (V : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ V))
      have hexp3 : (1 : ℝ) ≤ Real.exp 3 := by
        apply Real.one_le_exp
        norm_num
      have hle : Real.log (V : ℝ) ≤ Real.log (Real.exp 3 * (V : ℝ)) := by
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < V))
        have hVnn : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
        calc (V : ℝ) = 1 * (V : ℝ) := by ring
          _ ≤ Real.exp 3 * (V : ℝ) := mul_le_mul_of_nonneg_right hexp3 hVnn
      have hsq : (Real.log (V : ℝ)) ^ 2 ≤ (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hlogVnn hle 2
      have hfac : (∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
            * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)))
          = 2 * (∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
              * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      rw [hfac]
      calc 2 * (∑ d ∈ Finset.Icc 1 V, ((Nat.divisors d).card : ℝ) / (d : ℝ)
              * (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1)))
          ≤ 2 * (Cw * (∑ f ∈ Finset.Icc 1 V, H f)) := by
            exact mul_le_mul_of_nonneg_left (hbase V) (by norm_num)
        _ ≤ 2 * (Cw * (Ct * (Real.log (V : ℝ)) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hU hCwpos.le
        _ ≤ max (2 * Cw * Ct) (max (2 * Cw) 1) * (Real.log (Real.exp 3 * (V : ℝ))) ^ 2 := by
            have hconst : 2 * Cw * Ct ≤ max (2 * Cw * Ct) (max (2 * Cw) 1) := le_max_left _ _
            have h1 : 2 * (Cw * (Ct * (Real.log (V : ℝ)) ^ 2))
                = (2 * Cw * Ct) * (Real.log (V : ℝ)) ^ 2 := by ring
            rw [h1]
            exact mul_le_mul hconst hsq (sq_nonneg _) hCmax_nonneg
    · -- V ≤ 1
      have hVle : V ≤ 1 := by omega
      interval_cases V
      · -- V = 0
        have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by simp
        rw [h0, Finset.sum_empty]
        simp [Real.log_zero]
      · -- V = 1
        have hS1 : (∑ d ∈ Finset.Icc 1 1, ((Nat.divisors d).card : ℝ) / (d : ℝ)
            * (2 * ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1))) = 2 := by
          rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide]
          simp [Nat.divisors_one, Nat.primeFactors_one]
        rw [hS1]
        have hlog : Real.log (Real.exp 3 * ((1 : ℕ) : ℝ)) = 3 := by
          rw [Nat.cast_one, mul_one, Real.log_exp]
        rw [hlog]
        nlinarith [hCmax_ge_1]

end

end Commons.NumberTheory.DivisorBound
