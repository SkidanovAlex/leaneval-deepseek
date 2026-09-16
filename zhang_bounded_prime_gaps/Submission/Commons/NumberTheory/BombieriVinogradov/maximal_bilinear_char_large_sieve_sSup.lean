import Mathlib
import Submission.Commons.Analysis.Perron.bilinear_perron_bound
import Submission.Commons.Analysis.Sum.min_log_ratio_sum_le
import Submission.Commons.Analysis.Integral.inv_sqrt_sq_sum_integral_le
import Submission.Commons.NumberTheory.BombieriVinogradov.char_large_sieve_twisted_rpow
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_error_sum_bound
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_main_term_integral
import Submission.Commons.NumberTheory.BombieriVinogradov.bilinear_char_perron_bound
import Submission.Commons.NumberTheory.DirichletCharacter.norm_char_nat_le_one

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Classical
open Finset

noncomputable section

/-- The finset of primitive Dirichlet characters modulo `q`. -/
private def charFilt (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ

private lemma natCast_ne_add_half (n y : ℕ) : (n : ℝ) ≠ (y : ℝ) + 1 / 2 := by
  intro h
  have h2 : (2 * ((n : ℤ) - (y : ℤ)) : ℝ) = 1 := by
    have hh : (2 : ℝ) * ((n : ℝ) - (y : ℝ)) = 1 := by linarith
    push_cast at hh ⊢
    linarith
  have h3 : 2 * ((n : ℤ) - (y : ℤ)) = 1 := by exact_mod_cast h2
  omega

private lemma mul_lt_half_iff (m n y : ℕ) : ((m : ℝ) * (n : ℝ) < (y : ℝ) + 1 / 2) ↔ (m * n ≤ y) := by
  rw [← Nat.cast_mul]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have : (y : ℝ) + 1 ≤ ((m * n : ℕ) : ℝ) := by exact_mod_cast hc
    linarith
  · intro h
    have : ((m * n : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    linarith

theorem maximal_bilinear_char_large_sieve_sSup :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q M N : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hN : 1 ≤ N) (a b : ℕ → ℂ),
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                  (Classical.decPred _) Finset.univ),
            sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 (M * N)))
        ≤ c * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
            Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
            Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
  obtain ⟨Cperr, hCperr_pos, hCperr⟩ := bilinear_char_perron_bound
  obtain ⟨Cmain, hCmain_pos, hCmain⟩ := bilinear_main_term_integral
  refine ⟨3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1, by positivity, ?_⟩
  intro Q M N hQ hM hN a b
  classical
  set K : ℕ := M * N with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hKcast : (K : ℝ) = (M : ℝ) * (N : ℝ) := by rw [hK]; push_cast; ring
  have hMN1 : (1:ℝ) ≤ (M:ℝ) * (N:ℝ) := by
    have h1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have h2 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    nlinarith
  set Tr : ℝ := (M : ℝ) * (N : ℝ) with hTr
  have hTrpos : 0 < Tr := by rw [hTr]; positivity
  have hTrnn : 0 ≤ Tr := le_of_lt hTrpos
  set Lg : ℝ := Real.log (2 * (M : ℝ) * (N : ℝ) + 2) with hLg
  have hXpos : 0 < 2 * (M : ℝ) * (N : ℝ) + 2 := by positivity
  have hLgpos : 0 < Lg := by
    rw [hLg]; exact Real.log_pos (by linarith)
  have hLg1 : 1 ≤ Lg := by
    rw [hLg]
    have h4 : 1 ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
      linarith [Real.exp_one_lt_three]
    apply le_trans h4
    apply Real.log_le_log (by norm_num)
    linarith
  set c0 : ℝ := 1 / Lg with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0mul : c0 * Lg = 1 := by rw [hc0]; field_simp
  have hKpow : ((K : ℝ) + 1 / 2) ^ c0 ≤ Real.exp 1 := by
    have hKle : (K : ℝ) + 1 / 2 ≤ 2 * (M : ℝ) * (N : ℝ) + 2 := by
      rw [hKcast]; linarith [hMN1]
    have hmono := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (K:ℝ)+1/2) hKle hc0pos.le
    calc ((K : ℝ) + 1 / 2) ^ c0 ≤ (2 * (M : ℝ) * (N : ℝ) + 2) ^ c0 := hmono
      _ = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hXpos, ← hLg]
          congr 1
          rw [mul_comm, hc0mul]
  have hlogTr : Real.log (2 * Tr / c0 + 2) ≤ 3 * Lg := by
    have hTr_eq : Tr = (M : ℝ) * (N : ℝ) := hTr
    have hLgX : Lg ≤ 2 * (M : ℝ) * (N : ℝ) + 2 := by
      rw [hLg]; exact Real.log_le_self (by positivity)
    have hargpos : 0 < 2 * Tr / c0 + 2 := by rw [hTr]; positivity
    have harg_eq : 2 * Tr / c0 + 2 = (2 * (M : ℝ) * (N : ℝ)) * Lg + 2 := by
      rw [hTr_eq, hc0]
      field_simp
    have hX4 : 4 ≤ 2 * (M : ℝ) * (N : ℝ) + 2 := by linarith [hMN1]
    have harg_le : 2 * Tr / c0 + 2 ≤ 2 * (2 * (M : ℝ) * (N : ℝ) + 2) ^ 2 := by
      rw [harg_eq]
      have hA0 : (0:ℝ) ≤ 2 * (M:ℝ) * (N:ℝ) := by positivity
      have h1 : 2*(M:ℝ)*(N:ℝ) * Lg ≤ 2*(M:ℝ)*(N:ℝ) * (2*(M:ℝ)*(N:ℝ)+2) :=
        mul_le_mul_of_nonneg_left hLgX hA0
      nlinarith [h1, hA0, hX4, sq_nonneg (2 * (M : ℝ) * (N : ℝ) + 2)]
    calc Real.log (2 * Tr / c0 + 2) ≤ Real.log (2 * (2 * (M : ℝ) * (N : ℝ) + 2) ^ 2) :=
          Real.log_le_log hargpos harg_le
      _ = Real.log 2 + 2 * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; ring
      _ ≤ 3 * Lg := by
          have hlog2 : Real.log 2 ≤ Real.log (2 * (M : ℝ) * (N : ℝ) + 2) :=
            Real.log_le_log (by norm_num) (by linarith)
          rw [hLg]; linarith
  set A2 : ℝ := ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 with hA2
  set B2 : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 with hB2
  have hA2nn : 0 ≤ A2 := by rw [hA2]; positivity
  have hB2nn : 0 ≤ B2 := by rw [hB2]; positivity
  set Rr : ℝ := Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * A2) *
      Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * B2) with hRr
  have hRrnn : 0 ≤ Rr := by rw [hRr]; positivity
  set Ebound : ℝ := Real.exp 1 * (100 * Lg) * Real.sqrt A2 * Real.sqrt B2 with hEbound
  have hweight : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ))
      ≤ (Q : ℝ) ^ 2 := by
    have hcard : ∀ q, 1 ≤ q → (((charFilt q).card : ℕ) : ℝ) ≤ (q.totient : ℝ) := by
      intro q hq1
      haveI : NeZero q := ⟨by omega⟩
      have h1 : (charFilt q).card ≤ Fintype.card (DirichletCharacter ℂ q) := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      rw [← h2]
      exact_mod_cast h1
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ))
        ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * (q.totient : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (hcard q (Finset.mem_Icc.mp hq).1)
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mem_Icc] at hq
          have hφ : (q.totient : ℝ) ≠ 0 := by
            have hpos : 0 < q := by omega
            have : 0 < q.totient := Nat.totient_pos.mpr hpos
            positivity
          rw [div_mul_cancel₀ _ hφ]
      _ ≤ (Q : ℝ) ^ 2 := by
          have hstep : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ (∑ q ∈ Finset.Icc 1 Q, (Q : ℝ)) := by
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_Icc] at hq
            exact Nat.cast_le.mpr hq.2
          have hcard2 : (∑ q ∈ Finset.Icc 1 Q, (Q : ℝ)) = (Q : ℝ) ^ 2 := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
            ring
          linarith [hstep, hcard2.le]
  have hQR : (Q : ℝ) ^ 2 * Real.sqrt A2 * Real.sqrt B2 ≤ Rr := by
    rw [hRr, Real.sqrt_mul (by positivity) A2, Real.sqrt_mul (by positivity) B2]
    have hMQ : (Q : ℝ) ≤ Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) := by
      have hsq : Real.sqrt ((Q : ℝ) ^ 2) = Q := Real.sqrt_sq (by positivity)
      rw [← hsq]
      apply Real.sqrt_le_sqrt
      nlinarith [show (0:ℝ) ≤ (M:ℝ) by positivity]
    have hNQ : (Q : ℝ) ≤ Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) := by
      have hsq : Real.sqrt ((Q : ℝ) ^ 2) = Q := Real.sqrt_sq (by positivity)
      rw [← hsq]
      apply Real.sqrt_le_sqrt
      nlinarith [show (0:ℝ) ≤ (N:ℝ) by positivity]
    have step1 : Q * Q ≤ Real.sqrt ((M:ℝ)+(Q:ℝ)^2) * Real.sqrt ((N:ℝ)+(Q:ℝ)^2) :=
      mul_le_mul hMQ hNQ (by positivity) (Real.sqrt_nonneg _)
    rw [show (Q:ℝ)^2 * Real.sqrt A2 * Real.sqrt B2
          = Q * Q * (Real.sqrt A2 * Real.sqrt B2) by ring]
    calc Q * Q * (Real.sqrt A2 * Real.sqrt B2)
        ≤ (Real.sqrt ((M:ℝ)+(Q:ℝ)^2) * Real.sqrt ((N:ℝ)+(Q:ℝ)^2)) * (Real.sqrt A2 * Real.sqrt B2) :=
          mul_le_mul_of_nonneg_right step1 (by positivity)
      _ = Real.sqrt ((M:ℝ)+(Q:ℝ)^2) * Real.sqrt A2
            * (Real.sqrt ((N:ℝ)+(Q:ℝ)^2) * Real.sqrt B2) := by ring
  have hper : ∀ (q : ℕ), 1 ≤ q → ∀ χ ∈ charFilt q,
      sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
            '' Set.Icc 1 K)
      ≤ (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
          (∫ t in (-Tr)..Tr,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖)
        + Cperr * Ebound := by
    intro q hq1 χ hχmem
    haveI : NeZero q := ⟨by omega⟩
    have hχ : χ.IsPrimitive := by
      rw [charFilt] at hχmem
      exact (Finset.mem_filter.mp hχmem).2
    apply csSup_le
    · exact ⟨_, 1, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hK1⟩, rfl⟩
    · intro bb hbb
      rcases hbb with ⟨y, hy, rfl⟩
      rw [Set.mem_Icc] at hy
      obtain ⟨hy1, hy2⟩ := hy
      have hyR : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
      have hyKR : (y : ℝ) ≤ (K : ℝ) := by exact_mod_cast hy2
      have hbound := hCperr q χ M N a b c0 ((y : ℝ) + 1 / 2) Tr hc0pos
        (by linarith) hTrpos (fun n => natCast_ne_add_half n y)
      have hcut : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if (m : ℝ) * (n : ℝ) < (y : ℝ) + 1 / 2 then (1 : ℂ) else 0) * a m * b n *
              χ ((m * n : ℕ) : ZMod q))
          = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q) := by
        apply Finset.sum_congr rfl; intro m hm
        apply Finset.sum_congr rfl; intro n hn
        rw [if_congr (mul_lt_half_iff m n y) rfl rfl]
      rw [hcut] at hbound
      have hxK : (y : ℝ) + 1 / 2 ≤ (M : ℝ) * (N : ℝ) + 1 := by
        rw [hKcast] at hyKR; linarith
      have herr : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * (((y : ℝ) + 1 / 2) / ((m : ℝ) * (n : ℝ))) ^ c0 *
              min 1 (1 / (Tr * |Real.log (((y : ℝ) + 1 / 2) / ((m : ℝ) * (n : ℝ)))|))) ≤ Ebound := by
        rw [hEbound, hLg, hc0, hTr]
        exact bilinear_error_sum_bound M N hM hN ((y : ℝ) + 1 / 2) (by linarith) hxK a b
      have hxpow : ((y : ℝ) + 1 / 2) ^ c0 ≤ ((K : ℝ) + 1 / 2) ^ c0 := by
        apply Real.rpow_le_rpow (by positivity) _ hc0pos.le
        linarith
      have hIntnn : 0 ≤ (∫ t in (-Tr)..Tr,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖) := by
        apply intervalIntegral.integral_nonneg_of_forall (by linarith [hTrnn])
        intro t
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      refine le_trans hbound ?_
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxpow (by positivity)) hIntnn
      · exact mul_le_mul_of_nonneg_left herr hCperr_pos.le
  have hper2 : ∀ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 K)
      ≤ (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
            (((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
              (∫ t in (-Tr)..Tr,
                ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                 (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
          + (Cperr * Ebound) * (((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ)) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hw : 0 ≤ ((q : ℝ) / (q.totient : ℝ)) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hstep1 : (∑ χ ∈ charFilt q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 K))
        ≤ (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
              (∑ χ ∈ charFilt q,
                (∫ t in (-Tr)..Tr,
                  ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                   (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                  / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
            + (Cperr * Ebound) * (((charFilt q).card : ℕ) : ℝ) := by
      have h1 := Finset.sum_le_sum (fun χ hχ => hper q hq1 χ hχ)
      have h2 : (∑ χ ∈ charFilt q,
            ((1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
                (∫ t in (-Tr)..Tr,
                  ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                   (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                  / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖)
              + (Cperr * Ebound)))
          = (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
              (∑ χ ∈ charFilt q,
                (∫ t in (-Tr)..Tr,
                  ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                   (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                  / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
            + (Cperr * Ebound) * (((charFilt q).card : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
      exact le_trans h1 (le_of_eq h2)
    calc ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 K)
        ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
                (∑ χ ∈ charFilt q,
                  (∫ t in (-Tr)..Tr,
                    ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                     (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                    / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
              + (Cperr * Ebound) * (((charFilt q).card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep1 hw
      _ = (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
            (((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
              (∫ t in (-Tr)..Tr,
                ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                 (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
          + (Cperr * Ebound) * (((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ)) := by
          ring
  have hmain : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ charFilt q,
          (∫ t in (-Tr)..Tr,
            ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
             (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
            / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
      ≤ Cmain * Rr * Real.log (2 * Tr / c0 + 2) := by
    have h := hCmain Q M N hQ hM hN c0 hc0pos a b
    rw [← hTr] at h
    rw [← hA2, ← hB2] at h
    have hgroup : Cmain * (Real.sqrt (((M:ℝ)+(Q:ℝ)^2) * A2) * Real.sqrt (((N:ℝ)+(Q:ℝ)^2) * B2))
          * Real.log (2 * Tr / c0 + 2)
        = Cmain * Real.sqrt (((M:ℝ)+(Q:ℝ)^2) * A2) * Real.sqrt (((N:ℝ)+(Q:ℝ)^2) * B2)
          * Real.log (2 * Tr / c0 + 2) := by ring
    rw [hRr, hgroup]
    simpa only [charFilt] using h
  have hsum_le : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ charFilt q,
            sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 K))
      ≤ (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
          + (Cperr * Ebound) * ((Q : ℝ) ^ 2) := by
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ charFilt q,
            sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 K))
        ≤ ∑ q ∈ Finset.Icc 1 Q,
            ((1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
                (((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
                  (∫ t in (-Tr)..Tr,
                    ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                     (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                    / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
              + (Cperr * Ebound) * (((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ))) :=
          Finset.sum_le_sum hper2
      _ = (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 *
              (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * ∑ χ ∈ charFilt q,
                (∫ t in (-Tr)..Tr,
                  ‖(∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) * ((m : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I))) *
                   (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) * ((n : ℂ)) ^ (-((c0 : ℂ) + (t : ℂ) * Complex.I)))‖
                  / ‖(c0 : ℂ) + (t : ℂ) * Complex.I‖))
            + (Cperr * Ebound) * (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * (((charFilt q).card : ℕ) : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
            + (Cperr * Ebound) * ((Q : ℝ) ^ 2) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left hmain (by positivity)
          · apply mul_le_mul_of_nonneg_left hweight (by positivity)
  have hfinal : (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
        + (Cperr * Ebound) * ((Q : ℝ) ^ 2)
      ≤ (3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1) * Rr * Lg := by
    have hlogargnn : 0 ≤ Real.log (2 * Tr / c0 + 2) := by
      apply Real.log_nonneg
      have : 0 < 2 * Tr / c0 := by rw [hTr]; positivity
      linarith
    have h1 : (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
        ≤ (3 * Real.exp 1 * Cmain / (2 * Real.pi)) * Rr * Lg := by
      have hinner : (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * Real.log (2 * Tr / c0 + 2)
          ≤ (3 * Real.exp 1 / (2 * Real.pi)) * Lg := by
        have hA : (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 ≤ (1 / (2 * Real.pi)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left hKpow (by positivity)
        have hmul : (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * Real.log (2 * Tr / c0 + 2)
            ≤ (1 / (2 * Real.pi)) * Real.exp 1 * (3 * Lg) := by
          rw [show (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * Real.log (2 * Tr / c0 + 2)
              = ((1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0) * Real.log (2 * Tr / c0 + 2) by ring]
          rw [show (1 / (2 * Real.pi)) * Real.exp 1 * (3 * Lg)
              = ((1 / (2 * Real.pi)) * Real.exp 1) * (3 * Lg) by ring]
          exact mul_le_mul hA hlogTr hlogargnn (by positivity)
        calc _ ≤ (1 / (2 * Real.pi)) * Real.exp 1 * (3 * Lg) := hmul
          _ = (3 * Real.exp 1 / (2 * Real.pi)) * Lg := by ring
      calc (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
          = (Cmain * Rr) * ((1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * Real.log (2 * Tr / c0 + 2)) := by ring
        _ ≤ (Cmain * Rr) * ((3 * Real.exp 1 / (2 * Real.pi)) * Lg) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = (3 * Real.exp 1 * Cmain / (2 * Real.pi)) * Rr * Lg := by ring
    have h2 : (Cperr * Ebound) * ((Q : ℝ) ^ 2) ≤ (100 * Real.exp 1 * Cperr) * Rr * Lg := by
      have hE : Ebound = Real.exp 1 * (100 * Lg) * Real.sqrt A2 * Real.sqrt B2 := hEbound
      have hsub : Ebound * ((Q : ℝ) ^ 2) ≤ Real.exp 1 * (100 * Lg) * Rr := by
        rw [hE]
        calc Real.exp 1 * (100 * Lg) * Real.sqrt A2 * Real.sqrt B2 * (Q : ℝ) ^ 2
            = Real.exp 1 * (100 * Lg) * ((Q : ℝ) ^ 2 * Real.sqrt A2 * Real.sqrt B2) := by ring
          _ ≤ Real.exp 1 * (100 * Lg) * Rr :=
              mul_le_mul_of_nonneg_left hQR (by positivity)
      calc (Cperr * Ebound) * ((Q : ℝ) ^ 2) = Cperr * (Ebound * ((Q : ℝ) ^ 2)) := by ring
        _ ≤ Cperr * (Real.exp 1 * (100 * Lg) * Rr) := mul_le_mul_of_nonneg_left hsub (le_of_lt hCperr_pos)
        _ = (100 * Real.exp 1 * Cperr) * Rr * Lg := by ring
    calc (1 / (2 * Real.pi)) * ((K : ℝ) + 1 / 2) ^ c0 * (Cmain * Rr * Real.log (2 * Tr / c0 + 2))
          + (Cperr * Ebound) * ((Q : ℝ) ^ 2)
        ≤ (3 * Real.exp 1 * Cmain / (2 * Real.pi)) * Rr * Lg
          + (100 * Real.exp 1 * Cperr) * Rr * Lg := add_le_add h1 h2
      _ ≤ (3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1) * Rr * Lg := by
          have hnn : 0 ≤ Rr * Lg := mul_nonneg hRrnn (le_of_lt hLgpos)
          nlinarith [hnn]
  have key : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ charFilt q,
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 K))
      ≤ (3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1) * Rr * Lg :=
    le_trans hsum_le hfinal
  have hgroup2 : (3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1)
        * (Real.sqrt (((M:ℝ)+(Q:ℝ)^2) * A2) * Real.sqrt (((N:ℝ)+(Q:ℝ)^2) * B2)) * Lg
      = (3 * Real.exp 1 * Cmain / (2 * Real.pi) + 100 * Real.exp 1 * Cperr + 1)
        * Real.sqrt (((M:ℝ)+(Q:ℝ)^2) * A2) * Real.sqrt (((N:ℝ)+(Q:ℝ)^2) * B2) * Lg := by ring
  rw [hRr] at key
  rw [← hgroup2]
  simpa only [charFilt] using key

end

end Commons.NumberTheory.BombieriVinogradov
