import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4_defs
import Submission.Work.BMF.n4_exp_log_cpow
import Submission.Work.BMF.n4Wr_integrable
import Submission.Work.BMF.n4_cpow_norm
import Submission.Work.BMF.n4_moment_integral
import Submission.Work.BMF.n4_psi_torsion_card
import Submission.Work.BMF.n4_torsion_bound
import Submission.Work.BMF.n4_perr_defs
import Submission.Work.BMF.n4_mv_bound
import Submission.Work.BMF.prime_char_sum_window
import Submission.Work.BMF.n4_numerics_small_q_12
import Submission.Work.BMF.n4_psum_of_window

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N4, Case B: the analytic range `q ≤ (log P)^{ℓ+4}`

The proof of `Work.BMF.n4_case_small_q` (see the route in the docstring of the theorem):
`n4_count_le_integral`-type reduction (proved here), the pointwise prime-character bound
`n4_psum_of_window` (fed by `prime_char_sum_window`, the N4a window estimate), the mean-value
bound `n4_mv_bound`, the torsion count `n4_psi_torsion_card`/`n4_torsion_bound`, the moment
integral `n4_moment_integral`, and the numerical comparisons `n4_numerics_small_q_12`.

Everything in this file is proved; the statements used from other modules are the nodes
`n4_mv_bound`, `prime_char_sum_window`, `n4_numerics_small_q_12`, `n4_psum_of_window`.
-/

namespace Work.BMF

open Finset Real MeasureTheory
open scoped BigOperators ComplexConjugate

set_option maxHeartbeats 1000000

/-! ## 1. Elementary facts about the Fejér weight `n4Wr` -/

private lemma n4Wr_nonneg' {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (ξ : ℝ) : 0 ≤ n4Wr C₀ ξ := by
  rw [n4Wr]
  exact mul_nonneg (by linarith) (le_max_right _ _)

private lemma n4Wr_le' {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (ξ : ℝ) : n4Wr C₀ ξ ≤ 12 * C₀ := by
  rw [n4Wr]
  have h : max (1 - 4 * C₀ * |ξ|) 0 ≤ 1 := by
    rw [max_le_iff]
    exact ⟨by nlinarith [abs_nonneg ξ, hC₀], by norm_num⟩
  calc 12 * C₀ * max (1 - 4 * C₀ * |ξ|) 0 ≤ 12 * C₀ * 1 :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ = 12 * C₀ := by ring

private lemma n4Wr_eq_zero' {C₀ ξ : ℝ} (hC₀ : 0 < C₀) (h : 1 / (4 * C₀) ≤ |ξ|) :
    n4Wr C₀ ξ = 0 := by
  rw [n4Wr]
  have h4 : 0 < 4 * C₀ := by linarith
  have h1 : 1 ≤ 4 * C₀ * |ξ| := by
    rw [div_le_iff₀ h4] at h; linarith
  rw [max_eq_right (show 1 - 4 * C₀ * |ξ| ≤ 0 by linarith), mul_zero]

private lemma n4Wr_div_eq_zero' {C₀ N t : ℝ} (hC₀ : 0 < C₀) (hN : 0 < N)
    (h : Real.pi * N / (2 * C₀) ≤ |t|) : n4Wr C₀ (t / (2 * Real.pi * N)) = 0 := by
  refine n4Wr_eq_zero' hC₀ ?_
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * N)]
  have hkey : 1 / (4 * C₀) * (2 * Real.pi * N) = Real.pi * N / (2 * C₀) := by
    field_simp; ring
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi * N)]
  rw [hkey]; exact h

/-! ## 2. The range check `|2πNξ| ≤ exp((log P)^{21/20})` -/

private lemma n4_exp_range_aux (ℓ : ℕ) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ (P N C₀ : ℝ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → ∀ ξ : ℝ, |ξ| ≤ 1 / (4 * C₀) →
      |2 * Real.pi * N * ξ| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓpos
  · refine ⟨1, le_refl 1, ?_⟩
    intro P N C₀ hP hN hNP hC₀ ξ hξ
    exfalso
    have h1 : P ^ (ℓ - 1) = 1 := by
      rw [Nat.sub_eq_zero_of_le (by omega : ℓ ≤ 1), pow_zero]
    rw [h1] at hNP
    linarith
  by_cases hℓ1 : ℓ = 1
  · refine ⟨1, le_refl 1, ?_⟩
    intro P N C₀ hP hN hNP hC₀ ξ hξ
    exfalso
    have h1 : P ^ (ℓ - 1) = 1 := by
      rw [Nat.sub_eq_zero_of_le (by omega : ℓ ≤ 1), pow_zero]
    rw [h1] at hNP
    linarith
  have hℓ2 : 2 ≤ ℓ := by omega
  set X : ℝ := max (((2 * ((ℓ : ℝ) + 1)) ^ (20 : ℕ))) 4 with hX
  refine ⟨max 1 (Real.exp X), le_max_left _ _, ?_⟩
  intro P N C₀ hP hN hNP hC₀ ξ hξ
  have hP1 : 1 ≤ P := le_trans (le_max_left _ _) hP
  have hPpos : 0 < P := by linarith
  have hExpX : Real.exp X ≤ P := le_trans (le_max_right _ _) hP
  have hLX : X ≤ Real.log P := by
    have h2 : Real.log (Real.exp X) ≤ Real.log P :=
      (Real.log_le_log_iff (Real.exp_pos X) hPpos).2 hExpX
    rwa [Real.log_exp] at h2
  have hX4 : 4 ≤ X := le_max_right _ _
  have hL4 : 4 ≤ Real.log P := le_trans hX4 hLX
  have hLpos : 0 < Real.log P := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (one_div_pos.mpr hLpos) hC₀
  have hNpos : 0 < N := by linarith
  have hP2 : 2 ≤ P := by
    have h1 : (1:ℝ) ≤ X := by linarith
    have h2 : Real.exp 1 ≤ Real.exp X := Real.exp_le_exp.mpr h1
    have h3 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  -- step 1: `|2πNξ| ≤ πN/(2C₀)`
  have step1 : |2 * Real.pi * N * ξ| ≤ Real.pi * N / (2 * C₀) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi * N)]
    have h2 : 2 * Real.pi * N * (1 / (4 * C₀)) = Real.pi * N / (2 * C₀) := by
      field_simp
      ring
    calc 2 * Real.pi * N * |ξ| ≤ 2 * Real.pi * N * (1 / (4 * C₀)) :=
          mul_le_mul_of_nonneg_left hξ (by positivity)
      _ = Real.pi * N / (2 * C₀) := h2
  -- step 2: `πN/(2C₀) ≤ πN log P/2`
  have hC₀inv : 1 / C₀ ≤ Real.log P := by
    rw [div_le_iff₀ hC₀pos]
    calc (1 : ℝ) = (1 / Real.log P) * Real.log P := by
          rw [one_div, inv_mul_cancel₀ hLpos.ne']
      _ ≤ C₀ * Real.log P := mul_le_mul_of_nonneg_right hC₀ hLpos.le
      _ = Real.log P * C₀ := by ring
  have step2 : Real.pi * N / (2 * C₀) ≤ Real.pi * N * Real.log P / 2 := by
    have h2 : 0 ≤ Real.pi * N / 2 := by positivity
    have h3 : Real.pi * N / (2 * C₀) = Real.pi * N / 2 * (1 / C₀) := by
      field_simp
    rw [h3]
    calc Real.pi * N / 2 * (1 / C₀) ≤ Real.pi * N / 2 * Real.log P :=
          mul_le_mul_of_nonneg_left hC₀inv h2
      _ = Real.pi * N * Real.log P / 2 := by ring
  -- step 3: `N ≤ P^{ℓ-1}`
  have hPpow : 0 < P ^ (ℓ - 1) := pow_pos hPpos _
  have step3 : Real.pi * N * Real.log P / 2 ≤ Real.pi * P ^ (ℓ - 1) * Real.log P / 2 := by
    have h : Real.pi * N ≤ Real.pi * P ^ (ℓ - 1) :=
      mul_le_mul_of_nonneg_left hNP Real.pi_pos.le
    have hL2 : 0 ≤ Real.log P / 2 := by linarith
    nlinarith [h, hL2]
  -- step 4: `π P^{ℓ-1} L / 2 ≤ exp (L^{21/20})`
  have hlog2 : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP2
  have hLrpow : ((2 * ((ℓ : ℝ) + 1)) ^ (20 : ℕ) : ℝ) ^ (1 / 20 : ℝ) = 2 * ((ℓ : ℝ) + 1) := by
    have hx : (0 : ℝ) < 2 * ((ℓ : ℝ) + 1) := by positivity
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    norm_num
  have hLip : (ℓ : ℝ) + 1 ≤ (Real.log P) ^ (1 / 20 : ℝ) := by
    have h1 : ((2 * ((ℓ : ℝ) + 1)) ^ (20 : ℕ) : ℝ) ≤ Real.log P :=
      le_trans (le_max_left _ _) hLX
    have h2 : 2 * ((ℓ : ℝ) + 1) ≤ (Real.log P) ^ (1 / 20 : ℝ) := by
      calc 2 * ((ℓ : ℝ) + 1) = ((2 * ((ℓ : ℝ) + 1)) ^ (20 : ℕ) : ℝ) ^ (1 / 20 : ℝ) := hLrpow.symm
        _ ≤ (Real.log P) ^ (1 / 20 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (ℓ : ℝ) + 1 ≤ 2 * ((ℓ : ℝ) + 1) := by linarith
    linarith
  have step4a : Real.pi * P ^ (ℓ - 1) * Real.log P / 2 ≤ 2 * P ^ ℓ := by
    have hpi2 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    have hLleP : Real.log P ≤ P := by
      have := Real.log_le_sub_one_of_pos hPpos
      linarith
    have h3 : Real.pi * Real.log P / 2 ≤ 2 * P := by
      have h4 : Real.pi / 2 * Real.log P ≤ 2 * Real.log P :=
        mul_le_mul_of_nonneg_right hpi2 hLpos.le
      calc Real.pi * Real.log P / 2 = Real.pi / 2 * Real.log P := by ring
        _ ≤ 2 * Real.log P := h4
        _ ≤ 2 * P := by linarith
    calc Real.pi * P ^ (ℓ - 1) * Real.log P / 2
        = P ^ (ℓ - 1) * (Real.pi * Real.log P / 2) := by ring
      _ ≤ P ^ (ℓ - 1) * (2 * P) := mul_le_mul_of_nonneg_left h3 (le_of_lt hPpow)
      _ = 2 * P ^ ℓ := by
          have h2 : P ^ (ℓ - 1) * P = P ^ ℓ := by
            conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ ℓ), pow_succ]
          rw [← h2]; ring
  have step4b : 2 * P ^ ℓ ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := by
    have hpos : 0 < 2 * P ^ ℓ := by positivity
    rw [← Real.log_le_log_iff hpos (Real.exp_pos _), Real.log_exp]
    rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hPpos _)), Real.log_pow]
    have hA : (Real.log P) ^ (21 / 20 : ℝ) = Real.log P * (Real.log P) ^ (1 / 20 : ℝ) := by
      rw [show (21 / 20 : ℝ) = 1 + 1 / 20 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
    rw [hA]
    have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : Real.log 2 + (ℓ : ℝ) * Real.log P ≤ ((ℓ : ℝ) + 1) * Real.log P := by
      have h3 : Real.log 2 ≤ Real.log P := hlog2
      nlinarith [hlog2nn]
    have h4 : ((ℓ : ℝ) + 1) * Real.log P ≤ Real.log P * (Real.log P) ^ (1 / 20 : ℝ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hLip hLpos.le
    linarith
  calc |2 * Real.pi * N * ξ| ≤ Real.pi * N / (2 * C₀) := step1
    _ ≤ Real.pi * N * Real.log P / 2 := step2
    _ ≤ Real.pi * P ^ (ℓ - 1) * Real.log P / 2 := step3
    _ ≤ 2 * P ^ ℓ := step4a
    _ ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := step4b


/-! ## 3. Basic binomial bound -/

private lemma add_pow_mul_le' {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E) (n : ℕ) :
    (M + E) ^ n ≤ 2 ^ n * (M ^ n + E ^ n) := by
  have h1 : M + E ≤ 2 * max M E := by
    have h2 : M ≤ max M E := le_max_left _ _
    have h3 : E ≤ max M E := le_max_right _ _
    linarith
  have hmax : 0 ≤ max M E := le_trans hM (le_max_left _ _)
  have h3 : (M + E) ^ n ≤ (2 * max M E) ^ n := pow_le_pow_left₀ (by linarith) h1 n
  have h4 : (max M E) ^ n ≤ M ^ n + E ^ n := by
    rcases le_total M E with h | h
    · rw [max_eq_right h]; have : 0 ≤ M ^ n := pow_nonneg hM n; linarith
    · rw [max_eq_left h]; have : 0 ≤ E ^ n := pow_nonneg hE n; linarith
  calc (M + E) ^ n ≤ (2 * max M E) ^ n := h3
    _ = 2 ^ n * (max M E) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (M ^ n + E ^ n) := mul_le_mul_of_nonneg_left h4 (by positivity)

/-! ## 4. The norm of the pair correlation -/

private lemma n4_norm_n4corr_le' (ℓ m : ℕ) {P : ℝ} {q : ℕ} (hP : 0 ≤ P) (hq : 1 ≤ q) (t : ℝ) :
    ‖n4corr ℓ m P q t‖ ≤ ((q.totient : ℝ))⁻¹ *
      ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  have hφpos : (0:ℝ) < (q.totient : ℝ) := by
    have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h1
  rw [n4corr_eq hP hq t, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ ψ : DirichletCharacter ℂ q,
        (psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ)‖
      ≤ ∑ ψ : DirichletCharacter ℂ q,
          ‖(psum P q (ψ ^ m) t) ^ ℓ * conj ((psum P q (ψ ^ m) t) ^ ℓ)‖ := norm_sum_le _ _
    _ = ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) := by
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        simp only [norm_mul, norm_pow, Complex.norm_conj]
        rw [← pow_add]
        congr 1
        ring

/-! ## 5. Counting characters -/

private lemma n4_chi_card (q : ℕ) [NeZero q] :
    (Fintype.card (DirichletCharacter ℂ q) : ℝ) = (q.totient : ℝ) := by
  have h := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at h
  rw [h]

private lemma n4_chi_torsion_le (q m : ℕ) [NeZero q] (hm : 1 ≤ m) :
    ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ^ m = 1)).card : ℝ)
      ≤ ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card := by
  have h1 := n4_psi_torsion_card q m
  have h2 := n4_torsion_bound q m hm
  rw [← h1] at h2
  exact h2

/-! ## 6. The pointwise bound for the pair correlation -/

private lemma n4_char_sum_bound {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) {P : ℝ} {q : ℕ} [NeZero q]
    {A Ce : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hCe : 0 ≤ Ce) {t : ℝ}
    (hbound : ∀ χ : DirichletCharacter ℂ q,
      ‖psum P q χ t‖ ≤ A * (if χ = 1 then (1:ℝ) else 0) + Ce) :
    ‖n4corr ℓ m P q t‖ ≤ 2 ^ (2 * ℓ) *
      ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) *
        (A ^ (2 * ℓ) + Ce ^ (2 * ℓ)) + Ce ^ (2 * ℓ)) := by
  classical
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hφpos : (0:ℝ) < (q.totient : ℝ) := by
    have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast h1
  have h2l : 2 * ℓ ≠ 0 := by omega
  have hkey : ∀ χ : DirichletCharacter ℂ q, ‖psum P q χ t‖ ^ (2 * ℓ) ≤
      2 ^ (2 * ℓ) * (A ^ (2 * ℓ) * (if χ = 1 then (1:ℝ) else 0) + Ce ^ (2 * ℓ)) := by
    intro χ
    have h1 := hbound χ
    have h2 := add_pow_mul_le' (M := A * (if χ = 1 then (1:ℝ) else 0)) (E := Ce)
      (by positivity) hCe (2 * ℓ)
    calc ‖psum P q χ t‖ ^ (2 * ℓ)
        ≤ (A * (if χ = 1 then (1:ℝ) else 0) + Ce) ^ (2 * ℓ) :=
          pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ ≤ 2 ^ (2 * ℓ) * ((A * (if χ = 1 then (1:ℝ) else 0)) ^ (2 * ℓ) + Ce ^ (2 * ℓ)) := h2
      _ = 2 ^ (2 * ℓ) * (A ^ (2 * ℓ) * (if χ = 1 then (1:ℝ) else 0) + Ce ^ (2 * ℓ)) := by
          rcases eq_or_ne χ 1 with hh | hh
          · subst hh; simp
          · rw [if_neg hh, mul_zero, zero_pow h2l, mul_zero, zero_add]
  have hsplit : ∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)
      = (∑ ψ : DirichletCharacter ℂ q, (if ψ ^ m = 1 then ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) else 0))
        + (∑ ψ : DirichletCharacter ℂ q,
            (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    by_cases h : ψ ^ m = 1 <;> simp [h]
  have hA1 : (∑ ψ : DirichletCharacter ℂ q,
        (if ψ ^ m = 1 then ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) else 0))
      ≤ ((Finset.univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ^ m = 1)).card : ℝ)
          * (2 ^ (2 * ℓ) * (A ^ (2 * ℓ) + Ce ^ (2 * ℓ))) := by
    rw [← Finset.sum_filter]
    calc ∑ ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ^ m = 1),
            ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)
        ≤ ∑ _ψ ∈ Finset.univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ^ m = 1),
            (2 ^ (2 * ℓ) * (A ^ (2 * ℓ) + Ce ^ (2 * ℓ))) := by
          refine Finset.sum_le_sum (fun ψ hψ => ?_)
          rw [Finset.mem_filter] at hψ
          have h := hkey (ψ ^ m)
          rw [if_pos hψ.2, mul_one] at h
          exact h
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hA2 : (∑ ψ : DirichletCharacter ℂ q, (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)))
      ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) * (2 ^ (2 * ℓ) * Ce ^ (2 * ℓ)) := by
    calc ∑ ψ : DirichletCharacter ℂ q, (if ψ ^ m = 1 then 0 else ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ))
        ≤ ∑ _ψ : DirichletCharacter ℂ q, (2 ^ (2 * ℓ) * Ce ^ (2 * ℓ)) := by
          refine Finset.sum_le_sum (fun ψ _ => ?_)
          by_cases h : ψ ^ m = 1
          · rw [if_pos h]; positivity
          · rw [if_neg h]
            have h' := hkey (ψ ^ m)
            rw [if_neg h, mul_zero, zero_add] at h'
            exact h'
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hr := n4_chi_torsion_le q m hm
  have hcard := n4_chi_card q
  have hcorr := n4_norm_n4corr_le' ℓ m hP hq1 t
  have hsum : (∑ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ))
      ≤ ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card * (2 ^ (2 * ℓ) * (A ^ (2 * ℓ) + Ce ^ (2 * ℓ)))
        + (q.totient : ℝ) * (2 ^ (2 * ℓ) * Ce ^ (2 * ℓ)) := by
    rw [hsplit]
    refine le_trans (add_le_add hA1 hA2) ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hr (by positivity)
    · rw [hcard]
  calc ‖n4corr ℓ m P q t‖ ≤ (q.totient : ℝ)⁻¹ * _ := hcorr
    _ ≤ (q.totient : ℝ)⁻¹ *
          (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card * (2 ^ (2 * ℓ) * (A ^ (2 * ℓ) + Ce ^ (2 * ℓ)))
            + (q.totient : ℝ) * (2 ^ (2 * ℓ) * Ce ^ (2 * ℓ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 ^ (2 * ℓ) *
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) *
            (A ^ (2 * ℓ) + Ce ^ (2 * ℓ)) + Ce ^ (2 * ℓ)) := by
        field_simp
        try ring

private lemma n4_corr_large_bound {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) {P : ℝ} {q : ℕ} [NeZero q]
    {A Ce : ℝ} (hP : 0 ≤ P) (hCe : 0 ≤ Ce) (hA : A ≤ Ce) {t : ℝ}
    (hbound : ∀ χ : DirichletCharacter ℂ q,
      ‖psum P q χ t‖ ≤ A * (if χ = 1 then (1:ℝ) else 0) + Ce) :
    ‖n4corr ℓ m P q t‖
      ≤ (q.totient : ℝ)⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
          ((2 * Ce) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2)) := by
  classical
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcorr := n4_norm_n4corr_le' ℓ m hP hq1 t
  have hpt : ∀ ψ : DirichletCharacter ℂ q, ‖psum P q (ψ ^ m) t‖ ≤ 2 * Ce := by
    intro ψ
    have h := hbound (ψ ^ m)
    rcases eq_or_ne (ψ ^ m) 1 with hh | hh
    · rw [if_pos hh, mul_one] at h; linarith
    · rw [if_neg hh, mul_zero, zero_add] at h; linarith
  have hpow : ∀ ψ : DirichletCharacter ℂ q,
      ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ) ≤ (2 * Ce) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2) := by
    intro ψ
    have h1 : 2 * ℓ = (2 * ℓ - 2) + 2 := by omega
    calc ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ)
        = ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2) * ‖psum P q (ψ ^ m) t‖ ^ 2 := by
          conv_lhs => rw [h1]
          rw [pow_add]
      _ ≤ ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2) * (2 * Ce) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hp := hpt ψ
          have hn := norm_nonneg (psum P q (ψ ^ m) t)
          nlinarith [hp, hn]
      _ = (2 * Ce) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2) := by ring
  calc ‖n4corr ℓ m P q t‖ ≤ (q.totient : ℝ)⁻¹ * _ := hcorr
    _ ≤ (q.totient : ℝ)⁻¹ *
          ∑ ψ : DirichletCharacter ℂ q, ((2 * Ce) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ψ _ => hpow ψ)) (by positivity)


/-! ## 7. The Fourier / majorant step -/

private noncomputable def n4pairW' {ℓ : ℕ} (m : ℕ) (q : ℕ) (N : ℝ)
    (v : (Fin ℓ → ℕ) × (Fin ℓ → ℕ)) (ξ : ℝ) : ℂ :=
  if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
    ((tprod v.2 : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ))
      * conj ((tprod v.1 : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ))))
  else 0

private noncomputable def n4gW' {ℓ : ℕ} (m : ℕ) (q : ℕ) (N C₀ : ℝ)
    (v : (Fin ℓ → ℕ) × (Fin ℓ → ℕ)) : ℝ :=
  if (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q] then
    n4w C₀ (N * (Real.log (tprod v.2 : ℝ) - Real.log (tprod v.1 : ℝ))) else 0

private lemma n4_exp_pair (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (N ξ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((ξ : ℂ) * (((N * (Real.log (B : ℝ) - Real.log (A : ℝ)) : ℝ)) : ℂ)))
      = (B : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ))
        * conj ((A : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ))) := by
  have h := n4_exp_log_cpow A B hA hB (2 * Real.pi * N * ξ)
  simp only [Complex.star_def] at h
  rw [← h]
  congr 1
  push_cast
  ring

private lemma n4_pair_fourier_f {ℓ : ℕ} {P N C₀ : ℝ} {q : ℕ} (hP : 1 ≤ P) (hC₀ : 0 < C₀)
    {v : (Fin ℓ → ℕ) × (Fin ℓ → ℕ)} (hv : v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ)) :
    (n4w C₀ (N * (Real.log (tprod v.2 : ℝ) - Real.log (tprod v.1 : ℝ))) : ℂ)
      = ∫ ξ : ℝ, n4W C₀ ξ *
          ((tprod v.2 : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ))
            * conj ((tprod v.1 : ℂ) ^ (Complex.I * (((2 * Real.pi * N * ξ : ℝ)) : ℂ)))) := by
  classical
  rw [Finset.mem_product] at hv
  have hP0 : (0:ℝ) ≤ P := by linarith
  have htprodpos : ∀ {w : Fin ℓ → ℕ}, w ∈ tup P q ℓ → 0 < tprod w := by
    intro w hw
    have h1 : (1:ℝ) ≤ P ^ ℓ := by
      simpa using pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) hP ℓ
    have h2 : P ^ ℓ ≤ (tprod w : ℝ) := tprod_ge hP0 hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1 h2))
  have hA : 0 < tprod v.1 := htprodpos hv.1
  have hB : 0 < tprod v.2 := htprodpos hv.2
  rw [(n4_majorant C₀ hC₀).2.2
      (N * (Real.log (tprod v.2 : ℝ) - Real.log (tprod v.1 : ℝ)))]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [n4_exp_pair (tprod v.1) (tprod v.2) hA hB N ξ]

private lemma n4_count_le_integral_f {ℓ m : ℕ} {P N C₀ : ℝ} {q : ℕ} (hP : 1 ≤ P) (hN : 3 ≤ N)
    (hC₀ : 0 < C₀) :
    ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ ∫ ξ : ℝ, n4Wr C₀ ξ * ‖n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ := by
  classical
  have hP0 : (0:ℝ) ≤ P := by linarith
  have hCnn : ∀ u : ℝ, 0 ≤ n4Wr C₀ u := by
    intro u
    rw [n4Wr]
    exact mul_nonneg (mul_nonneg (by norm_num) hC₀.le) (le_max_right _ _)
  have hIntWr : Integrable (fun ξ : ℝ => n4Wr C₀ ξ) := n4Wr_integrable hC₀
  have hnormW : ∀ ξ : ℝ, ‖n4W C₀ ξ‖ = n4Wr C₀ ξ := by
    intro ξ
    rw [n4W_apply]
    rw [show ‖((n4Wr C₀ ξ : ℝ) : ℂ)‖ = |n4Wr C₀ ξ| from by simp, abs_of_nonneg (hCnn ξ)]
  have htprodpos : ∀ {w : Fin ℓ → ℕ}, w ∈ tup P q ℓ → 0 < tprod w := by
    intro w hw
    have h1 : (1:ℝ) ≤ P ^ ℓ := by
      simpa using pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) hP ℓ
    have h2 : P ^ ℓ ≤ (tprod w : ℝ) := tprod_ge hP0 hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1 h2))
  have hsum_corr : ∀ ξ : ℝ, (∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4pairW' m q N v ξ)
      = n4corr ℓ m P q (2 * Real.pi * N * ξ) := by
    intro ξ
    simp only [n4corr, n4pairW']
  have hcard : ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4gW' m q N C₀ v := by
    simpa only [n4gW'] using
      n4_count_le_sum (ℓ:=ℓ) (m:=m) (P:=P) (N:=N) (C₀:=C₀) (q:=q) hP hN hC₀
  have hpair : ∀ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
      ((if (tprod v.2)^m ≡ (tprod v.1)^m [MOD q] then (1:ℝ) else 0 : ℝ) : ℂ)
        * (n4w C₀ (N * (Real.log (tprod v.2 : ℝ) - Real.log (tprod v.1 : ℝ))) : ℂ)
      = ∫ ξ : ℝ, n4W C₀ ξ * n4pairW' m q N v ξ := by
    intro v hv
    by_cases hc : (tprod v.2)^m ≡ (tprod v.1)^m [MOD q]
    · rw [if_pos hc, Complex.ofReal_one, one_mul]
      have hvw : (fun ξ : ℝ => n4W C₀ ξ * n4pairW' m q N v ξ)
          = fun ξ : ℝ => n4W C₀ ξ *
              ((tprod v.2 : ℂ) ^ (Complex.I * ((2 * Real.pi * N * ξ : ℝ) : ℂ))
                * conj ((tprod v.1 : ℂ) ^ (Complex.I * ((2 * Real.pi * N * ξ : ℝ) : ℂ)))) := by
        funext ξ; rw [n4pairW', if_pos hc]
      rw [hvw]
      exact n4_pair_fourier_f hP hC₀ hv
    · rw [if_neg hc, Complex.ofReal_zero, zero_mul]
      have hvw : (fun ξ : ℝ => n4W C₀ ξ * n4pairW' m q N v ξ) = fun _ : ℝ => (0 : ℂ) := by
        funext ξ; rw [n4pairW', if_neg hc, mul_zero]
      rw [hvw, integral_zero]
  have hint : ∀ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
      Integrable (fun ξ : ℝ => n4W C₀ ξ * n4pairW' m q N v ξ) := by
    intro v hv
    rw [Finset.mem_product] at hv
    have hApos : 0 < tprod v.1 := htprodpos hv.1
    have hBpos : 0 < tprod v.2 := htprodpos hv.2
    have hAne : (tprod v.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hApos.ne'
    have hBne : (tprod v.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hBpos.ne'
    refine Integrable.mono hIntWr ?_ ?_
    · apply Continuous.aestronglyMeasurable
      by_cases hc : (tprod v.2)^m ≡ (tprod v.1)^m [MOD q]
      · simp only [n4pairW', if_pos hc]
        have hexp : Continuous (fun ξ : ℝ => Complex.I * ((2 * Real.pi * N * ξ : ℝ) : ℂ)) := by
          fun_prop
        have hBc : Continuous (fun ξ : ℝ =>
            (tprod v.2 : ℂ) ^ (Complex.I * ((2 * Real.pi * N * ξ : ℝ) : ℂ))) :=
          hexp.const_cpow (Or.inl hBne)
        have hAc : Continuous (fun ξ : ℝ =>
            (tprod v.1 : ℂ) ^ (Complex.I * ((2 * Real.pi * N * ξ : ℝ) : ℂ))) :=
          hexp.const_cpow (Or.inl hAne)
        have hn4W : Continuous (fun ξ : ℝ => n4W C₀ ξ) := by
          simp only [n4W_apply]
          exact Complex.continuous_ofReal.comp (by unfold n4Wr; fun_prop)
        exact hn4W.mul (hBc.mul (Complex.continuous_conj.comp hAc))
      · simp only [n4pairW', if_neg hc, mul_zero]
        exact continuous_const
    · filter_upwards with ξ
      have hVle : ‖n4pairW' m q N v ξ‖ ≤ 1 := by
        by_cases hc : (tprod v.2)^m ≡ (tprod v.1)^m [MOD q]
        · rw [n4pairW', if_pos hc]
          rw [n4_cpow_norm (tprod v.1) (tprod v.2) hApos hBpos (2 * Real.pi * N * ξ)]
        · rw [n4pairW', if_neg hc, norm_zero]; norm_num
      rw [norm_mul, hnormW ξ, Real.norm_eq_abs, abs_of_nonneg (hCnn ξ)]
      calc n4Wr C₀ ξ * ‖n4pairW' m q N v ξ‖ ≤ n4Wr C₀ ξ * 1 :=
            mul_le_mul_of_nonneg_left hVle (hCnn ξ)
        _ = n4Wr C₀ ξ := mul_one _
  have hterm : ∀ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ),
      ((n4gW' m q N C₀ v : ℝ) : ℂ)
        = ((if (tprod v.2)^m ≡ (tprod v.1)^m [MOD q] then (1:ℝ) else 0 : ℝ) : ℂ)
          * (n4w C₀ (N * (Real.log (tprod v.2 : ℝ) - Real.log (tprod v.1 : ℝ))) : ℂ) := by
    intro v hv
    by_cases hc : (tprod v.2)^m ≡ (tprod v.1)^m [MOD q]
    · rw [n4gW', if_pos hc, if_pos hc, Complex.ofReal_one, one_mul]
    · rw [n4gW', if_neg hc, if_neg hc, Complex.ofReal_zero, zero_mul]
  have hll : ∀ ξ : ℝ, n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ)
      = ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4W C₀ ξ * n4pairW' m q N v ξ := by
    intro ξ
    rw [← hsum_corr ξ, Finset.mul_sum]
  have hmain : ((∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4gW' m q N C₀ v : ℝ) : ℂ)
      = ∫ ξ : ℝ, n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ) := by
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_congr rfl (fun v hv => hpair v hv)]
    rw [← MeasureTheory.integral_finsetSum ((tup P q ℓ) ×ˢ (tup P q ℓ))
        (fun v hv => hint v hv)]
    apply integral_congr_ae
    filter_upwards with ξ
    exact (hll ξ).symm
  have hZre : (∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4gW' m q N C₀ v)
      = (∫ ξ : ℝ, n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ)).re := by
    have := congrArg Complex.re hmain
    simpa using this
  calc ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ ∑ v ∈ (tup P q ℓ) ×ˢ (tup P q ℓ), n4gW' m q N C₀ v := hcard
    _ = (∫ ξ : ℝ, n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ)).re := hZre
    _ ≤ ‖∫ ξ : ℝ, n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ ξ : ℝ, ‖n4W C₀ ξ * n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, n4Wr C₀ ξ * ‖n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [norm_mul, hnormW ξ]

private lemma n4_cont_corr (ℓ m : ℕ) {P : ℝ} {q : ℕ} (hP : 1 ≤ P) :
    Continuous fun t : ℝ => n4corr ℓ m P q t := by
  classical
  unfold n4corr
  apply continuous_finsetSum
  intro v hv
  rw [Finset.mem_product] at hv
  have h0 : (0:ℝ) < P := by linarith
  have htpos : ∀ {w : Fin ℓ → ℕ}, w ∈ tup P q ℓ → 0 < tprod w := by
    intro w hw
    have h1 : (1:ℝ) ≤ P ^ ℓ := by
      simpa using pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) hP ℓ
    have h2 : P ^ ℓ ≤ (tprod w : ℝ) := tprod_ge h0.le hw
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_trans h1 h2))
  have h1ne : (tprod v.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (htpos hv.1).ne'
  have h2ne : (tprod v.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (htpos hv.2).ne'
  by_cases hc : (tprod v.2) ^ m ≡ (tprod v.1) ^ m [MOD q]
  · simp only [if_pos hc]
    have hexp : Continuous fun t : ℝ => Complex.I * (t : ℂ) := by fun_prop
    exact (hexp.const_cpow (Or.inl h2ne)).mul
      (Complex.continuous_conj.comp (hexp.const_cpow (Or.inl h1ne)))
  · simp only [if_neg hc]; exact continuous_const

private lemma n4_cont_psum {P : ℝ} {q : ℕ} (χ : DirichletCharacter ℂ q) (hP : 0 ≤ P) :
    Continuous fun t : ℝ => psum P q χ t := by
  classical
  unfold psum
  apply continuous_finsetSum
  intro p hp
  have hpne : (p : ℂ) ≠ 0 := by
    have := admP_prime hP hp
    exact_mod_cast this.ne_zero
  have hexp : Continuous fun t : ℝ => Complex.I * (t : ℂ) := by fun_prop
  exact continuous_const.mul (hexp.const_cpow (Or.inl hpne))

private lemma n4_integrable_one_add (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun t : ℝ => ((1 + |t|) ^ (2 * k))⁻¹) volume := by
  refine Integrable.mono' integrable_inv_one_add_sq ?_ ?_
  · have hcont : Continuous fun t : ℝ => ((1 + |t|) ^ (2 * k))⁻¹ := by
      apply Continuous.inv₀
      · fun_prop
      · intro t; positivity
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb1 : 0 < 1 + t ^ 2 := by positivity
    have hb : 1 + t ^ 2 ≤ (1 + |t|) ^ (2 * k) := by
      have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        rw [add_sq]; nlinarith [sq_abs t, abs_nonneg t]
      have h2 : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ (2 * k) :=
        pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le hb1 hb

private lemma n4_scale_integral_gen {C₀ N : ℝ} (f : ℝ → ℝ) (hN : 0 < N) :
    (∫ ξ : ℝ, n4Wr C₀ ξ * f (2 * Real.pi * N * ξ))
      = (1 / (2 * Real.pi * N)) * ∫ t : ℝ, n4Wr C₀ (t / (2 * Real.pi * N)) * f t := by
  set a : ℝ := 2 * Real.pi * N with ha
  have ha0 : a ≠ 0 := by rw [ha]; positivity
  have hann : 0 < a := by rw [ha]; positivity
  have h1 : (∫ ξ : ℝ, n4Wr C₀ ξ * f (2 * Real.pi * N * ξ))
      = ∫ ξ : ℝ, (fun t : ℝ => n4Wr C₀ (t / a) * f t) (a * ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    have hdiv : a * ξ / a = ξ := by rw [div_eq_iff ha0]; ring
    simp only [ha] at hdiv ⊢
    rw [hdiv]
  rw [h1, MeasureTheory.Measure.integral_comp_mul_left
    (g := fun t : ℝ => n4Wr C₀ (t / a) * f t) (a := a)]
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hann)]
  congr 1
  rw [ha]
  ring

private lemma n4_interval_integral_one_add (k : ℕ) (hk : 1 ≤ k) {E : ℝ} (hE : 0 ≤ E) :
    ∫ t in (-E)..E, ((1 + |t|) ^ (2 * k))⁻¹ ≤ 4 := by
  rw [intervalIntegral.integral_of_le (show -E ≤ E by linarith)]
  have hstep : ∫ t in Set.Ioc (-E) E, ((1 + |t|) ^ (2 * k))⁻¹ ∂volume
      ≤ ∫ t : ℝ, ((1 + |t|) ^ (2 * k))⁻¹ ∂volume := by
    have hfnn : ∀ t : ℝ, 0 ≤ ((1 + |t|) ^ (2 * k))⁻¹ := fun t => by positivity
    exact MeasureTheory.integral_mono_measure
      (μ := volume.restrict (Set.Ioc (-E) E)) (ν := volume)
      (f := fun t : ℝ => ((1 + |t|) ^ (2 * k))⁻¹)
      Measure.restrict_le_self
      (Filter.Eventually.of_forall hfnn)
      (n4_integrable_one_add k hk)
  exact le_trans hstep (n4_moment_integral k hk)

/-- Interval split: `f` is bounded by `g1` on `[-E,E]` and by `g2` where `|x| ≥ E`. -/
private lemma n4_interval_split {T E : ℝ} {f g1 g2 : ℝ → ℝ}
    (hf : Continuous f) (hg1 : Continuous g1) (hg2 : Continuous g2)
    (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hnn1 : ∀ x ∈ Set.Icc (-E) E, 0 ≤ g1 x)
    (hnn2 : ∀ x ∈ Set.Icc (-T) T, 0 ≤ g2 x)
    (h1 : ∀ x ∈ Set.Icc (-E) E, f x ≤ g1 x)
    (h2 : ∀ x ∈ Set.Icc (-T) T, E ≤ |x| → f x ≤ g2 x) :
    ∫ x in (-T)..T, f x ≤ (∫ x in (-E)..E, g1 x) + ∫ x in (-T)..T, g2 x := by
  have hIf : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hI1 : ∀ a b : ℝ, IntervalIntegrable g1 volume a b := fun a b => hg1.intervalIntegrable a b
  have hI2 : ∀ a b : ℝ, IntervalIntegrable g2 volume a b := fun a b => hg2.intervalIntegrable a b
  by_cases hET : E ≤ T
  · have hTEnn : -T ≤ -E := by linarith
    have hEnn : -E ≤ E := by linarith
    have hsum1 := intervalIntegral.integral_add_adjacent_intervals (hIf (-T) (-E)) (hIf (-E) E)
    have hsum2 := intervalIntegral.integral_add_adjacent_intervals (hIf (-T) E) (hIf E T)
    have hg2sum1 := intervalIntegral.integral_add_adjacent_intervals (hI2 (-T) (-E)) (hI2 (-E) E)
    have hg2sum2 := intervalIntegral.integral_add_adjacent_intervals (hI2 (-T) E) (hI2 E T)
    have hp1 : ∀ x ∈ Set.Icc (-T) (-E), f x ≤ g2 x := by
      intro x hx
      rw [Set.mem_Icc] at hx
      refine h2 x (by rw [Set.mem_Icc]; exact ⟨by linarith [hx.1], by linarith [hx.2, hE, hET]⟩) ?_
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]
    have hm1 : ∫ x in (-T)..(-E), f x ≤ ∫ x in (-T)..(-E), g2 x :=
      intervalIntegral.integral_mono_on hTEnn (hIf _ _) (hI2 _ _) hp1
    have hm2 : ∫ x in (-E)..E, f x ≤ ∫ x in (-E)..E, g1 x :=
      intervalIntegral.integral_mono_on hEnn (hIf _ _) (hI1 _ _) h1
    have hp3 : ∀ x ∈ Set.Icc E T, f x ≤ g2 x := by
      intro x hx
      rw [Set.mem_Icc] at hx
      refine h2 x (by rw [Set.mem_Icc]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) ?_
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]
    have hm3 : ∫ x in E..T, f x ≤ ∫ x in E..T, g2 x :=
      intervalIntegral.integral_mono_on hET (hIf _ _) (hI2 _ _) hp3
    have hpnn : ∀ u ∈ Set.Icc (-E) E, 0 ≤ g2 u := by
      intro u hu
      rw [Set.mem_Icc] at hu
      exact hnn2 u (by rw [Set.mem_Icc]; exact ⟨by linarith [hu.1], by linarith [hu.2, hET]⟩)
    have hgnn : 0 ≤ ∫ x in (-E)..E, g2 x := intervalIntegral.integral_nonneg hEnn hpnn
    linarith [hsum1, hsum2, hg2sum1, hg2sum2, hm1, hm2, hm3, hgnn]
  · have hTE : T ≤ E := le_of_lt (not_le.mp hET)
    have hp1 : ∀ x ∈ Set.Icc (-T) T, f x ≤ g1 x := by
      intro x hx
      rw [Set.mem_Icc] at hx
      exact h1 x (by rw [Set.mem_Icc]; exact ⟨by linarith [hx.1], by linarith [hx.2, hTE]⟩)
    have hm1 : ∫ x in (-T)..T, f x ≤ ∫ x in (-T)..T, g1 x :=
      intervalIntegral.integral_mono_on (by linarith) (hIf _ _) (hI1 _ _) hp1
    have hae : 0 ≤ᵐ[volume.restrict (Set.Ioc (-E) E)] g1 := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun x hx => by
        exact hnn1 x (by rw [Set.mem_Icc]; exact ⟨le_of_lt hx.1, hx.2⟩))
    have hm2 : ∫ x in (-T)..T, g1 x ≤ ∫ x in (-E)..E, g1 x :=
      intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        hae (hI1 _ _)
    have hgnn : 0 ≤ ∫ x in (-T)..T, g2 x :=
      intervalIntegral.integral_nonneg (by linarith) hnn2
    linarith [hm1, hm2, hgnn]

private lemma n4_integral_brut {ℓ m : ℕ} (hm : 1 ≤ m) (hℓ2 : 2 ≤ ℓ)
    {P N C₀ : ℝ} {q : ℕ} [NeZero q]
    {C₁ c₁ Cmv Kc : ℝ} (hC₁ : 0 < C₁) (hc₁ : 0 < c₁) (hCmv : 0 < Cmv)
    (hKc1 : 1 ≤ Kc) (hKcC₁ : C₁ ≤ Kc)
    (hP : 1 ≤ P) (hN : 3 ≤ N) (hq : 1 ≤ q) (hC₀pos : 0 < C₀) (hLpos : 0 < Real.log P)
    (hNpos : 0 < N)
    (hexp1 : ∀ t : ℝ, |t| ≤ Real.pi * N / (2 * C₀) →
        |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)))
    (hpt : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) →
        ‖psum P q χ t‖ ≤ C₁ * pi0 P / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0)
          + (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))
              + C₁ * (q.primeFactors.card : ℝ)))
    (hAge : ∀ t : ℝ, Real.exp (c₁ * Real.log P ^ (1 / 12 : ℝ)) / (C₁ * Real.log P) ≤ |t| →
        C₁ * pi0 P / (1 + |t|) ≤
          Kc * (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)) + C₁ * (q.primeFactors.card : ℝ)))
    (hmv : ∀ χ : DirichletCharacter ℂ q,
        ∫ t in (-(Real.pi * N / (2 * C₀)))..(Real.pi * N / (2 * C₀)), ‖psum P q χ t‖ ^ (2 * ℓ - 2)
          ≤ Cmv * (Real.pi * N / (2 * C₀) + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) :
    ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ (1 / (2 * Real.pi * N)) *
          (12 * C₀ * (2 ^ (2 * ℓ) *
              ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) *
                ((C₁ * pi0 P) ^ (2 * ℓ) * 4
                  + (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))
                      + C₁ * (q.primeFactors.card : ℝ)) ^ (2 * ℓ)
                    * (2 * (Real.exp (c₁ * Real.log P ^ (1 / 12 : ℝ)) / (C₁ * Real.log P))))
                + (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))
                    + C₁ * (q.primeFactors.card : ℝ)) ^ (2 * ℓ)
                  * (2 * (Real.exp (c₁ * Real.log P ^ (1 / 12 : ℝ)) / (C₁ * Real.log P)))))
            + 48 * C₀ * Kc ^ 2 * (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))
                + C₁ * (q.primeFactors.card : ℝ)) ^ 2 * Cmv
              * (Real.pi * N / (2 * C₀) + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) := by
  classical
  set perr : ℝ := C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))
    + C₁ * (q.primeFactors.card : ℝ) with hperr
  set Ee : ℝ := Real.exp (c₁ * Real.log P ^ (1 / 12 : ℝ)) / (C₁ * Real.log P) with hEe
  set T : ℝ := Real.pi * N / (2 * C₀) with hT
  set phi : ℝ := (q.totient : ℝ) with hphi
  set Rc : ℝ := ((2 * m : ℕ) : ℝ) ^ q.primeFactors.card with hRc
  have hperrnn : 0 ≤ perr := by rw [hperr]; positivity
  have hEepos : 0 < Ee := by rw [hEe]; positivity
  have hTpos : 0 < T := by rw [hT]; positivity
  have hTnn : 0 ≤ T := le_of_lt hTpos
  have hEenn : 0 ≤ Ee := le_of_lt hEepos
  have hphipos : 0 < phi := by
    rw [hphi]
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hRcnn : 0 ≤ Rc := by rw [hRc]; positivity
  have hpinonneg : 0 ≤ pi0 P := by rw [pi0]; positivity
  -- pointwise bounds on the correlation
  have hG1 : ∀ t : ℝ, |t| ≤ Ee → |t| ≤ T → ‖n4corr ℓ m P q t‖ ≤
      2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi0 P / (1 + |t|)) ^ (2 * ℓ) + perr ^ (2 * ℓ))
        + perr ^ (2 * ℓ)) := by
    intro t ht htT
    have hx : |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := hexp1 t htT
    have h := n4_char_sum_bound (ℓ := ℓ) (m := m) (P := P) (q := q)
      (A := C₁ * pi0 P / (1 + |t|)) (Ce := perr)
      (hℓ := by omega) (hm := hm) (hP := by linarith) (hA := by positivity) (hCe := hperrnn)
      (t := t) (hbound := fun χ => hpt χ t hx)
    rw [← hphi, ← hRc] at h
    exact h
  have hKcnn : 0 ≤ Kc := le_trans zero_le_one hKc1
  have hKcperr : 0 ≤ Kc * perr := mul_nonneg hKcnn hperrnn
  have hG2 : ∀ t : ℝ, |t| ≤ T → Ee ≤ |t| → ‖n4corr ℓ m P q t‖ ≤
      phi⁻¹ * ∑ ψ : DirichletCharacter ℂ q, ((2 * (Kc * perr)) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2)) := by
    intro t htT ht
    have hx : |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := hexp1 t htT
    have hb : ∀ χ : DirichletCharacter ℂ q,
        ‖psum P q χ t‖ ≤ C₁ * pi0 P / (1 + |t|) * (if χ = 1 then (1:ℝ) else 0) + Kc * perr := by
      intro χ
      have h1 := hpt χ t hx
      have h2 : perr ≤ Kc * perr := le_mul_of_one_le_left hperrnn hKc1
      linarith
    have h := n4_corr_large_bound (ℓ := ℓ) (m := m) (P := P) (A := C₁ * pi0 P / (1 + |t|))
      (Ce := Kc * perr)
      (hℓ := by omega) (hP := by linarith) (hCe := hKcperr) (hA := hAge t ht) (hbound := hb)
    rw [← hphi] at h
    exact h
  -- the integrands
  set Wf : ℝ → ℝ := fun t => n4Wr C₀ (t / (2 * Real.pi * N)) with hWf
  set Ff : ℝ → ℝ := fun t => Wf t * ‖n4corr ℓ m P q t‖ with hFf
  set G1f : ℝ → ℝ := fun t => 2 ^ (2 * ℓ) * ((Rc / phi) *
      ((C₁ * pi0 P / (1 + |t|)) ^ (2 * ℓ) + perr ^ (2 * ℓ)) + perr ^ (2 * ℓ)) with hG1f
  set G2f : ℝ → ℝ := fun t => phi⁻¹ *
      ∑ ψ : DirichletCharacter ℂ q, ((2 * (Kc * perr)) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2)) with hG2f
  have hWcont : Continuous Wf := by
    rw [hWf]; unfold n4Wr; fun_prop
  have hG1cont : Continuous G1f := by
    rw [hG1f]
    have h1 : Continuous fun t : ℝ => (C₁ * pi0 P / (1 + |t|)) ^ (2 * ℓ) :=
      (Continuous.div₀ continuous_const (by fun_prop : Continuous fun t : ℝ => 1 + |t|)
        (fun t => by positivity)).pow _
    exact continuous_const.mul (continuous_const.mul (h1.add continuous_const) |>.add continuous_const)
  have hG2cont : Continuous G2f := by
    rw [hG2f]
    refine continuous_const.mul ?_
    exact continuous_finsetSum _ (fun ψ _ => continuous_const.mul
      (((n4_cont_psum (ψ ^ m) (by linarith : (0:ℝ) ≤ P)).norm).pow _))
  have hFcont : Continuous Ff := by
    rw [hFf]
    exact hWcont.mul (n4_cont_corr ℓ m hP).norm
  have hWle : ∀ t : ℝ, Wf t ≤ 12 * C₀ := fun t => by
    rw [hWf]; exact n4Wr_le' hC₀pos.le _
  have hWnn : ∀ t : ℝ, 0 ≤ Wf t := fun t => by
    rw [hWf]; exact n4Wr_nonneg' hC₀pos.le _
  have hG1nn : ∀ t : ℝ, 0 ≤ G1f t := fun t => by rw [hG1f]; positivity
  have hG2nn : ∀ t : ℝ, 0 ≤ G2f t := fun t => by rw [hG2f]; positivity
  -- integral reduction and change of variables
  have hcnt : ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ ∫ ξ : ℝ, n4Wr C₀ ξ * ‖n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ :=
    n4_count_le_integral_f (ℓ := ℓ) (m := m) (P := P) (N := N) (C₀ := C₀) (q := q) hP hN hC₀pos
  have hsub := n4_scale_integral_gen (C₀ := C₀) (N := N) (fun t : ℝ => ‖n4corr ℓ m P q t‖) hNpos
  -- the support of `Wf`
  have hsupp : (∫ t : ℝ, Ff t) = ∫ t in (-T)..T, Ff t := by
    have h0 : ∀ t ∉ Set.Ioc (-T) T, Ff t = 0 := by
      intro t ht
      have h1 : T ≤ |t| := by
        rw [Set.mem_Ioc, not_and_or] at ht
        rcases ht with h | h
        · push_neg at h
          rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_pos (by linarith)]
          linarith
      have h2 : Wf t = 0 := by
        rw [hWf]
        refine n4Wr_div_eq_zero' hC₀pos hNpos ?_
        rw [← hT]
        exact h1
      rw [hFf]
      show Wf t * ‖n4corr ℓ m P q t‖ = 0
      rw [h2, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0]
    rw [intervalIntegral.integral_of_le (show -T ≤ T by linarith)]
  -- the interval split
  set Ep : ℝ := min Ee T with hEp
  have hEpnn : 0 ≤ Ep := le_min hEenn hTnn
  have hEpleE : Ep ≤ Ee := min_le_left _ _
  have hEpleT : Ep ≤ T := min_le_right _ _
  have hsplit : ∫ t in (-T)..T, Ff t
      ≤ (∫ t in (-Ep)..Ep, Wf t * G1f t) + ∫ t in (-T)..T, Wf t * G2f t := by
    refine n4_interval_split hFcont (hWcont.mul hG1cont) (hWcont.mul hG2cont) hTnn hEpnn ?_ ?_ ?_ ?_
    · intro x _
      exact mul_nonneg (hWnn x) (hG1nn x)
    · intro x _
      exact mul_nonneg (hWnn x) (hG2nn x)
    · intro x hx
      rw [Set.mem_Icc] at hx
      have hxE : |x| ≤ Ep := by rw [abs_le]; exact hx
      exact mul_le_mul_of_nonneg_left (hG1 x (le_trans hxE hEpleE) (le_trans hxE hEpleT)) (hWnn x)
    · intro x hx hEx
      rw [Set.mem_Icc] at hx
      have hxT : |x| ≤ T := by rw [abs_le]; exact hx
      rcases le_total Ee T with hET | hTE
      · have hEp_eq : Ep = Ee := by rw [hEp]; exact min_eq_left hET
        exact mul_le_mul_of_nonneg_left (hG2 x hxT (by rwa [hEp_eq] at hEx)) (hWnn x)
      · have hEp_eq : Ep = T := by rw [hEp]; exact min_eq_right hTE
        have hW0 : Wf x = 0 := by
          rw [hWf]
          refine n4Wr_div_eq_zero' hC₀pos hNpos ?_
          rw [← hT]
          have : T ≤ |x| := by rwa [hEp_eq] at hEx
          exact this
        rw [hFf]
        show Wf x * ‖n4corr ℓ m P q x‖ ≤ Wf x * G2f x
        rw [hW0, zero_mul, zero_mul]
  -- bound the small-`|t|` part
  have hI1 : (∫ t in (-Ee)..Ee, Wf t * G1f t)
      ≤ 12 * C₀ * (2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi0 P) ^ (2 * ℓ) * 4
          + perr ^ (2 * ℓ) * (2 * Ee)) + perr ^ (2 * ℓ) * (2 * Ee))) := by
    have hmono : (∫ t in (-Ee)..Ee, Wf t * G1f t) ≤ ∫ t in (-Ee)..Ee, 12 * C₀ * G1f t :=
      intervalIntegral.integral_mono_on (by linarith : -Ee ≤ Ee)
        ((hWcont.mul hG1cont).intervalIntegrable _ _)
        ((continuous_const.mul hG1cont).intervalIntegrable _ _)
        (fun x _ => mul_le_mul_of_nonneg_right (hWle x) (hG1nn x))
    have hcm : (∫ t in (-Ee)..Ee, 12 * C₀ * G1f t) = 12 * C₀ * ∫ t in (-Ee)..Ee, G1f t :=
      intervalIntegral.integral_const_mul (12 * C₀) G1f
    rw [hcm] at hmono
    have hinner : (∫ t in (-Ee)..Ee, G1f t) ≤ 2 ^ (2 * ℓ) * ((Rc / phi) *
        ((C₁ * pi0 P) ^ (2 * ℓ) * 4 + perr ^ (2 * ℓ) * (2 * Ee)) + perr ^ (2 * ℓ) * (2 * Ee)) := by
      have hpt2 : ∀ x : ℝ, G1f x ≤ 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
          * ((1 + |x|) ^ (2 * ℓ))⁻¹ + 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1) := by
        intro x
        have hpow : (C₁ * pi0 P / (1 + |x|)) ^ (2 * ℓ)
            = (C₁ * pi0 P) ^ (2 * ℓ) * ((1 + |x|) ^ (2 * ℓ))⁻¹ := by
          rw [div_pow, div_eq_mul_inv]
        have heq : G1f x = 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
            * ((1 + |x|) ^ (2 * ℓ))⁻¹ + 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1) := by
          rw [hG1f]
          simp only []
          rw [hpow]
          ring
        rw [heq]
      have h1c : Continuous fun t : ℝ => 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
          * ((1 + |t|) ^ (2 * ℓ))⁻¹ := by
        refine continuous_const.mul ?_
        apply Continuous.inv₀
        · fun_prop
        · intro t; positivity
      have hmono2 : (∫ t in (-Ee)..Ee, G1f t)
          ≤ ∫ t in (-Ee)..Ee, (2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
              * ((1 + |t|) ^ (2 * ℓ))⁻¹ + 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1)) :=
        intervalIntegral.integral_mono_on (by linarith : -Ee ≤ Ee) (hG1cont.intervalIntegrable _ _)
          ((h1c.add continuous_const).intervalIntegrable _ _) (fun x _ => hpt2 x)
      have hadd : (∫ t in (-Ee)..Ee, (2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
            * ((1 + |t|) ^ (2 * ℓ))⁻¹ + 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1)))
          = (∫ t in (-Ee)..Ee, 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
              * ((1 + |t|) ^ (2 * ℓ))⁻¹)
            + ∫ t in (-Ee)..Ee, 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1) :=
        intervalIntegral.integral_add (h1c.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
      rw [hadd] at hmono2
      have hb1 : (∫ t in (-Ee)..Ee, 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ)
            * ((1 + |t|) ^ (2 * ℓ))⁻¹) ≤ 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ) * 4 := by
        rw [intervalIntegral.integral_const_mul (2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ))]
        exact mul_le_mul_of_nonneg_left (n4_interval_integral_one_add ℓ (by omega) hEenn)
          (by positivity)
      have hb2 : (∫ t in (-Ee)..Ee, 2 ^ (2 * ℓ) * perr ^ (2 * ℓ) * (Rc / phi + 1))
          = 2 ^ (2 * ℓ) * ((Rc / phi) * (perr ^ (2 * ℓ) * (2 * Ee))
              + perr ^ (2 * ℓ) * (2 * Ee)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      have hgoal : 2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi0 P) ^ (2 * ℓ) * 4
            + perr ^ (2 * ℓ) * (2 * Ee)) + perr ^ (2 * ℓ) * (2 * Ee))
          = 2 ^ (2 * ℓ) * (Rc / phi) * (C₁ * pi0 P) ^ (2 * ℓ) * 4
            + 2 ^ (2 * ℓ) * ((Rc / phi) * (perr ^ (2 * ℓ) * (2 * Ee))
                + perr ^ (2 * ℓ) * (2 * Ee)) := by
        ring
      rw [hgoal]
      linarith [hmono2, hb1, hb2]
    exact le_trans hmono (mul_le_mul_of_nonneg_left hinner (by positivity))
  -- bound the large-`|t|` part
  have hI2 : (∫ t in (-T)..T, Wf t * G2f t)
      ≤ 48 * C₀ * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1) := by
    have hmono : (∫ t in (-T)..T, Wf t * G2f t) ≤ ∫ t in (-T)..T, 12 * C₀ * G2f t :=
      intervalIntegral.integral_mono_on (by linarith : -T ≤ T)
        ((hWcont.mul hG2cont).intervalIntegrable _ _)
        ((continuous_const.mul hG2cont).intervalIntegrable _ _)
        (fun x _ => mul_le_mul_of_nonneg_right (hWle x) (hG2nn x))
    have hcm : (∫ t in (-T)..T, 12 * C₀ * G2f t) = 12 * C₀ * ∫ t in (-T)..T, G2f t :=
      intervalIntegral.integral_const_mul (12 * C₀) G2f
    rw [hcm] at hmono
    have hinner : (∫ t in (-T)..T, G2f t)
        ≤ 4 * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1) := by
      have hstep : (∫ t in (-T)..T, G2f t) = phi⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
          ∫ t in (-T)..T, ((2 * (Kc * perr)) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2)) := by
        rw [hG2f]
        rw [intervalIntegral.integral_const_mul (phi⁻¹)]
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        intro ψ _
        exact (continuous_const.mul
          (((n4_cont_psum (ψ ^ m) (by linarith : (0:ℝ) ≤ P)).norm).pow _)).intervalIntegrable _ _
      rw [hstep]
      have hb : ∀ ψ : DirichletCharacter ℂ q,
          ∫ t in (-T)..T, ((2 * (Kc * perr)) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2))
            ≤ (2 * (Kc * perr)) ^ 2 * (Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) := by
        intro ψ
        rw [intervalIntegral.integral_const_mul ((2 * (Kc * perr)) ^ 2)]
        exact mul_le_mul_of_nonneg_left (hmv (ψ ^ m)) (by positivity)
      have hb2 : phi⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
          ∫ t in (-T)..T, ((2 * (Kc * perr)) ^ 2 * ‖psum P q (ψ ^ m) t‖ ^ (2 * ℓ - 2))
          ≤ phi⁻¹ * ∑ _ψ : DirichletCharacter ℂ q,
            ((2 * (Kc * perr)) ^ 2 * (Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ψ _ => hb ψ)) (by positivity)
      refine le_trans hb2 ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = phi := by rw [n4_chi_card q, hphi]
      rw [hcard, ← mul_assoc, inv_mul_cancel₀ hphipos.ne', one_mul]
      apply le_of_eq
      ring
    have h12 : (0:ℝ) ≤ 12 * C₀ := by positivity
    calc (∫ t in (-T)..T, Wf t * G2f t) ≤ 12 * C₀ * ∫ t in (-T)..T, G2f t := hmono
      _ ≤ 12 * C₀ * (4 * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) :=
          mul_le_mul_of_nonneg_left hinner h12
      _ = 48 * C₀ * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1) := by ring
  have hI1ext : (∫ t in (-Ep)..Ep, Wf t * G1f t) ≤ ∫ t in (-Ee)..Ee, Wf t * G1f t := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_
      ((hWcont.mul hG1cont).intervalIntegrable _ _)
    exact Filter.Eventually.of_forall (fun x => mul_nonneg (hWnn x) (hG1nn x))
  -- assemble
  have hchain : ((n4set ℓ m P N C₀ q).card : ℝ)
      ≤ (1 / (2 * Real.pi * N)) *
          (12 * C₀ * (2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi0 P) ^ (2 * ℓ) * 4
              + perr ^ (2 * ℓ) * (2 * Ee)) + perr ^ (2 * ℓ) * (2 * Ee)))
            + 48 * C₀ * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) := by
    have h1 : (∫ ξ : ℝ, n4Wr C₀ ξ * ‖n4corr ℓ m P q (2 * Real.pi * N * ξ)‖) =
        (1 / (2 * Real.pi * N)) * ∫ t : ℝ, Ff t := by
      rw [hsub, hFf, hWf]
    calc ((n4set ℓ m P N C₀ q).card : ℝ)
        ≤ ∫ ξ : ℝ, n4Wr C₀ ξ * ‖n4corr ℓ m P q (2 * Real.pi * N * ξ)‖ := hcnt
      _ = (1 / (2 * Real.pi * N)) * ∫ t : ℝ, Ff t := h1
      _ = (1 / (2 * Real.pi * N)) * ∫ t in (-T)..T, Ff t := by rw [hsupp]
      _ ≤ (1 / (2 * Real.pi * N)) *
            ((∫ t in (-Ep)..Ep, Wf t * G1f t) + ∫ t in (-T)..T, Wf t * G2f t) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ ≤ (1 / (2 * Real.pi * N)) *
            ((∫ t in (-Ee)..Ee, Wf t * G1f t) + ∫ t in (-T)..T, Wf t * G2f t) :=
          mul_le_mul_of_nonneg_left (add_le_add hI1ext le_rfl) (by positivity)
      _ ≤ (1 / (2 * Real.pi * N)) *
            (12 * C₀ * (2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi0 P) ^ (2 * ℓ) * 4
                + perr ^ (2 * ℓ) * (2 * Ee)) + perr ^ (2 * ℓ) * (2 * Ee)))
              + 48 * C₀ * Kc ^ 2 * perr ^ 2 * Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hI1 hI2) (by positivity)
  refine le_trans hchain ?_
  rw [hperr, hEe, hT, hRc, hphi]
  try ring


-- (The numerical parameters `n4Perr`, `n4Eee`, `n4Rc` are imported from
-- `Submission.Work.BMF.n4_perr_defs`.)

/-- **The numerical comparison of N4, Case B.**  Turns the crude estimate of `n4_integral_brut`
into the final shape `C C₀ π₀(P)^{2ℓ}/N (R_m(q)/φ(q) + 1/log N)`. -/
private lemma n4_final_arith {ℓ m : ℕ} (hℓ2 : 2 ≤ ℓ)
    {C₁ c₁ Cmv Knum Kc : ℝ} (hC₁pos : 0 < C₁) (hCmvpos : 0 < Cmv) (hKnumpos : 0 < Knum)
    (hKc1 : 1 ≤ Kc) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ) (q : ℕ), 1 ≤ N → 0 < Real.log P → 0 < Real.log N →
      1 ≤ Real.log N → 1 ≤ Real.log P → 1 ≤ P → 1 ≤ q → 0 < C₀ →
      n4Perr C₁ c₁ P q ^ 2 * pi0 P ^ (ℓ - 1) * N * Real.log N ≤ Knum * C₀ * pi0 P ^ (2 * ℓ) →
      n4Perr C₁ c₁ P q ^ 2 * P ^ (ℓ - 1) * Real.log P * pi0 P ^ (ℓ - 1) * Real.log N
          ≤ Knum * pi0 P ^ (2 * ℓ) →
      n4Eee C₁ c₁ P * n4Perr C₁ c₁ P q ^ (2 * ℓ) * Real.log N * Real.log P
          ≤ Knum * pi0 P ^ (2 * ℓ) →
      (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
            (n4Rc m q / (q.totient : ℝ) *
              ((C₁ * pi0 P) ^ (2 * ℓ) * 4
                + n4Perr C₁ c₁ P q ^ (2 * ℓ) * (2 * n4Eee C₁ c₁ P))
              + n4Perr C₁ c₁ P q ^ (2 * ℓ) * (2 * n4Eee C₁ c₁ P)))
          + 48 * C₀ * Kc ^ 2 * n4Perr C₁ c₁ P q ^ 2 * Cmv
            * (Real.pi * N / (2 * C₀) + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1))
        ≤ C * C₀ * pi0 P ^ (2 * ℓ) / N * (n4Rc m q / (q.totient : ℝ) + 1 / Real.log N) := by
  classical
  set KA : ℝ := (24 / Real.pi) * 2 ^ (2 * ℓ) * C₁ ^ (2 * ℓ) with hKAdef
  set KB : ℝ := (12 / Real.pi) * 2 ^ (2 * ℓ) * Knum with hKBdef
  set KD : ℝ := 12 * Cmv * Kc ^ 2 * Knum with hKDdef
  set KE : ℝ := (24 / Real.pi) * Cmv * Kc ^ 2 * Knum with hKEdef
  have hKAnn : 0 ≤ KA := by rw [hKAdef]; positivity
  have hKBnn : 0 ≤ KB := by rw [hKBdef]; positivity
  have hKDnn : 0 ≤ KD := by rw [hKDdef]; positivity
  have hKEnn : 0 ≤ KE := by rw [hKEdef]; positivity
  refine ⟨KA + KB + KB + KD + KE + 1, by positivity, ?_⟩
  intro P N C₀ q hN1 hLpos hLNpos hLN1 hL1 hP1 hq1 hC₀pos h1 h2 h3
  classical
  set perr : ℝ := n4Perr C₁ c₁ P q with hperr
  set Ee : ℝ := n4Eee C₁ c₁ P with hEe
  set Rc : ℝ := n4Rc m q with hRc
  set pi : ℝ := pi0 P with hpi
  set L : ℝ := Real.log P with hL
  set LN : ℝ := Real.log N with hLN
  set phi : ℝ := (q.totient : ℝ) with hphi
  have hperrnn : 0 ≤ perr := by rw [hperr, n4Perr]; positivity
  have hEenn : 0 ≤ Ee := by rw [hEe, n4Eee]; positivity
  have hpinn : 0 ≤ pi := by rw [hpi, pi0]; positivity
  have hRcnn : 0 ≤ Rc := by rw [hRc, n4Rc]; positivity
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hLNnn : 0 ≤ LN := le_of_lt hLNpos
  have hNpos : 0 < N := by linarith
  have hLL1 : 1 ≤ LN * L := by nlinarith
  have d1 : perr ^ 2 * pi ^ (ℓ - 1) ≤ Knum * C₀ * pi ^ (2 * ℓ) / (N * LN) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < N * LN)]
    nlinarith [h1]
  have d2 : perr ^ 2 * P ^ (ℓ - 1) * L * pi ^ (ℓ - 1) ≤ Knum * pi ^ (2 * ℓ) / LN := by
    rw [le_div_iff₀ hLNpos]
    nlinarith [h2]
  have d3a : Ee * perr ^ (2 * ℓ) ≤ Knum * pi ^ (2 * ℓ) := by
    have hpnn : 0 ≤ Ee * perr ^ (2 * ℓ) := by positivity
    calc Ee * perr ^ (2 * ℓ) = Ee * perr ^ (2 * ℓ) * 1 := by ring
      _ ≤ Ee * perr ^ (2 * ℓ) * (LN * L) := mul_le_mul_of_nonneg_left hLL1 hpnn
      _ = Ee * perr ^ (2 * ℓ) * LN * L := by ring
      _ ≤ Knum * pi ^ (2 * ℓ) := h3
  have d3b : Ee * perr ^ (2 * ℓ) ≤ Knum * pi ^ (2 * ℓ) / LN := by
    rw [le_div_iff₀ hLNpos]
    have h0 : 0 ≤ Ee * perr ^ (2 * ℓ) * LN := by positivity
    calc Ee * perr ^ (2 * ℓ) * LN = Ee * perr ^ (2 * ℓ) * LN * 1 := by ring
      _ ≤ Ee * perr ^ (2 * ℓ) * LN * L := mul_le_mul_of_nonneg_left hL1 h0
      _ ≤ Knum * pi ^ (2 * ℓ) := h3
  have e1 : (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
        ((Rc / phi) * ((C₁ * pi) ^ (2 * ℓ) * 4))))
      ≤ (Rc / phi) * KA * (C₀ * pi ^ (2 * ℓ) / N) := by
    rw [hKAdef]
    apply le_of_eq
    ring
  have e2 : (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
        ((Rc / phi) * (perr ^ (2 * ℓ) * (2 * Ee)))))
      ≤ (Rc / phi) * KB * (C₀ * pi ^ (2 * ℓ) / N) := by
    rw [hKBdef]
    have hfac : 0 ≤ (Rc / phi) * ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) := by positivity
    calc (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
          ((Rc / phi) * (perr ^ (2 * ℓ) * (2 * Ee)))))
        = (Rc / phi) * ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) * (Ee * perr ^ (2 * ℓ)) := by ring
      _ ≤ (Rc / phi) * ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) * (Knum * pi ^ (2 * ℓ)) :=
          mul_le_mul_of_nonneg_left d3a hfac
      _ = (Rc / phi) * ((12 / Real.pi) * 2 ^ (2 * ℓ) * Knum) * (C₀ * pi ^ (2 * ℓ) / N) := by ring
  have e3 : (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
        (perr ^ (2 * ℓ) * (2 * Ee))))
      ≤ KB * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
    rw [hKBdef]
    have hfac : 0 ≤ ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) := by positivity
    calc (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) * (perr ^ (2 * ℓ) * (2 * Ee))))
        = ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) * (Ee * perr ^ (2 * ℓ)) := by ring
      _ ≤ ((12 / Real.pi) * 2 ^ (2 * ℓ)) * (C₀ / N) * (Knum * pi ^ (2 * ℓ) / LN) :=
          mul_le_mul_of_nonneg_left d3b hfac
      _ = ((12 / Real.pi) * 2 ^ (2 * ℓ) * Knum) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by ring
  have e4 : (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (Real.pi * N / (2 * C₀))
        * pi ^ (ℓ - 1)))
      ≤ KD * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
    rw [hKDdef]
    have hfac : 0 ≤ 12 * Cmv * Kc ^ 2 := by positivity
    calc (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (Real.pi * N / (2 * C₀))
          * pi ^ (ℓ - 1)))
        = 12 * Cmv * Kc ^ 2 * (perr ^ 2 * pi ^ (ℓ - 1)) := by
          field_simp
          try ring
      _ ≤ 12 * Cmv * Kc ^ 2 * (Knum * C₀ * pi ^ (2 * ℓ) / (N * LN)) :=
          mul_le_mul_of_nonneg_left d1 hfac
      _ = (12 * Cmv * Kc ^ 2 * Knum) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
          field_simp
          try ring
  have e5 : (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (P ^ (ℓ - 1) * L)
        * pi ^ (ℓ - 1)))
      ≤ KE * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
    rw [hKEdef]
    have hfac : 0 ≤ (24 / Real.pi) * Cmv * Kc ^ 2 * C₀ := by positivity
    calc (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (P ^ (ℓ - 1) * L)
          * pi ^ (ℓ - 1)))
        = (24 / Real.pi) * Cmv * Kc ^ 2 * C₀ * (perr ^ 2 * P ^ (ℓ - 1) * L * pi ^ (ℓ - 1)) / N := by
          field_simp
          try ring
      _ ≤ (24 / Real.pi) * Cmv * Kc ^ 2 * C₀ * (Knum * pi ^ (2 * ℓ) / LN) / N := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left d2 hfac
      _ = ((24 / Real.pi) * Cmv * Kc ^ 2 * Knum) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
          field_simp
          try ring
  have hexpand : (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) *
        (Rc / phi * ((C₁ * pi) ^ (2 * ℓ) * 4 + perr ^ (2 * ℓ) * (2 * Ee))
          + perr ^ (2 * ℓ) * (2 * Ee)))
      + 48 * C₀ * Kc ^ 2 * perr ^ 2 * Cmv * (Real.pi * N / (2 * C₀) + P ^ (ℓ - 1) * L) * pi ^ (ℓ - 1))
      = (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) * ((Rc / phi) * ((C₁ * pi) ^ (2 * ℓ) * 4))))
        + (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) * ((Rc / phi) * (perr ^ (2 * ℓ) * (2 * Ee)))))
        + (1 / (2 * Real.pi * N)) * (12 * C₀ * (2 ^ (2 * ℓ) * (perr ^ (2 * ℓ) * (2 * Ee))))
        + (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (Real.pi * N / (2 * C₀)) * pi ^ (ℓ - 1)))
        + (1 / (2 * Real.pi * N)) * (48 * C₀ * Kc ^ 2 * (perr ^ 2 * Cmv * (P ^ (ℓ - 1) * L) * pi ^ (ℓ - 1))) := by
    ring
  rw [hexpand]
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add e1 e2) e3) e4) e5) ?_
  have hphipos : 0 < phi := by
    rw [hphi]
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hRcphi : 0 ≤ Rc / phi := div_nonneg hRcnn hphipos.le
  have hCpi : 0 ≤ C₀ * pi ^ (2 * ℓ) / N := by positivity
  have hLNinv : 0 ≤ 1 / LN := by positivity
  have stepA : (Rc / phi) * KA * (C₀ * pi ^ (2 * ℓ) / N) + (Rc / phi) * KB * (C₀ * pi ^ (2 * ℓ) / N)
      ≤ (Rc / phi) * (KA + KB + KB + KD + KE + 1) * (C₀ * pi ^ (2 * ℓ) / N) := by
    have h : KA + KB ≤ KA + KB + KB + KD + KE + 1 := by linarith
    calc (Rc / phi) * KA * (C₀ * pi ^ (2 * ℓ) / N) + (Rc / phi) * KB * (C₀ * pi ^ (2 * ℓ) / N)
        = (Rc / phi) * (KA + KB) * (C₀ * pi ^ (2 * ℓ) / N) := by ring
      _ ≤ (Rc / phi) * (KA + KB + KB + KD + KE + 1) * (C₀ * pi ^ (2 * ℓ) / N) := by
          apply mul_le_mul_of_nonneg_right _ hCpi
          exact mul_le_mul_of_nonneg_left h hRcphi
  have stepB : KB * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) + KD * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
        + KE * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
      ≤ (KA + KB + KB + KD + KE + 1) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by
    have h : KB + KD + KE ≤ KA + KB + KB + KD + KE + 1 := by linarith
    have h1 : (KB + KD + KE) * (C₀ * pi ^ (2 * ℓ) / N)
        ≤ (KA + KB + KB + KD + KE + 1) * (C₀ * pi ^ (2 * ℓ) / N) :=
      mul_le_mul_of_nonneg_right h hCpi
    calc KB * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) + KD * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
          + KE * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
        = (KB + KD + KE) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) := by ring
      _ ≤ (KA + KB + KB + KD + KE + 1) * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) :=
          mul_le_mul_of_nonneg_right h1 hLNinv
  have hmid : (Rc / phi) * KA * (C₀ * pi ^ (2 * ℓ) / N) + (Rc / phi) * KB * (C₀ * pi ^ (2 * ℓ) / N)
        + KB * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) + KD * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
        + KE * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)
      = ((Rc / phi) * KA * (C₀ * pi ^ (2 * ℓ) / N) + (Rc / phi) * KB * (C₀ * pi ^ (2 * ℓ) / N))
        + ((KB * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN) + KD * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN))
          + KE * (C₀ * pi ^ (2 * ℓ) / N) * (1 / LN)) := by ring
  rw [hmid]
  refine le_trans (add_le_add stepA stepB) ?_
  apply le_of_eq
  ring


/-! ## 10. The conditional master theorem -/

private theorem n4_case_small_q_master (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    {c₁ C₁ Cmv Knum Kc : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hCmv : 0 < Cmv)
    (hKnum : 0 < Knum) (hKc1 : 1 ≤ Kc) (hKcC₁ : C₁ ≤ Kc)
    {Ppt Pmv Pnum Pexp : ℝ}
    (hpt : ∀ (P : ℝ), Ppt ≤ P → ∀ (q : ℕ), DecidableEq (DirichletCharacter ℂ q) →
        1 ≤ q → q ≤ (Real.log P) ^ (ℓ + 4) →
        ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) →
        ‖psum P q χ t‖ ≤ C₁ * pi0 P / (1 + |t|) *
            (@ite ℝ (χ = 1) (Classical.propDecidable _) 1 0)
          + n4Perr C₁ c₁ P q)
    (hmv : ∀ (P : ℝ), Pmv ≤ P → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ), 0 ≤ T →
        ∫ t in (-T)..T, ‖psum P q χ t‖ ^ (2 * ℓ - 2)
          ≤ Cmv * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1))
    (hnum : ∀ (P : ℝ), Pnum ≤ P → ∀ (N C₀ : ℝ) (q : ℕ), 3 ≤ N → N ≤ P ^ (ℓ - 1) →
        1 / Real.log P ≤ C₀ → 1 ≤ q → q ≤ (Real.log P) ^ (ℓ + 4) →
        n4Perr C₁ c₁ P q ^ 2 * pi0 P ^ (ℓ - 1) * N * Real.log N ≤ Knum * C₀ * pi0 P ^ (2 * ℓ) ∧
        n4Perr C₁ c₁ P q ^ 2 * P ^ (ℓ - 1) * Real.log P * pi0 P ^ (ℓ - 1) * Real.log N
            ≤ Knum * pi0 P ^ (2 * ℓ) ∧
        n4Eee C₁ c₁ P * n4Perr C₁ c₁ P q ^ (2 * ℓ) * Real.log N * Real.log P
            ≤ Knum * pi0 P ^ (2 * ℓ))
    (hExp : ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ (P N C₀ : ℝ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
        1 / Real.log P ≤ C₀ → ∀ ξ : ℝ, |ξ| ≤ 1 / (4 * C₀) →
        |2 * Real.pi * N * ξ| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ))) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
        1 / Real.log P ≤ C₀ → 1 ≤ q → q ≤ (Real.log P) ^ (ℓ + 4) →
        ((n4set ℓ m P N C₀ q).card : ℝ)
          ≤ C * C₀ * pi0 P ^ (2 * ℓ) / N *
              (n4Rc m q / (q.totient : ℝ) + 1 / Real.log N) := by
  obtain ⟨Pexp0, hPexp0, hexp0⟩ := hExp
  by_cases hℓ2 : 2 ≤ ℓ
  · obtain ⟨C, hCpos, harith⟩ := n4_final_arith (ℓ := ℓ) (m := m) hℓ2
      (C₁ := C₁) (c₁ := c₁) (Cmv := Cmv) (Knum := Knum) (Kc := Kc) hC₁ hCmv hKnum hKc1
    refine ⟨C, max (max Ppt Pmv) (max Pnum (max Pexp0 (max 8 (Real.exp 1)))), hCpos, ?_⟩
    intro P N C₀ q hP hN hNle hC₀ hq hqle
    rw [max_le_iff] at hP
    obtain ⟨hA, hB⟩ := hP
    rw [max_le_iff] at hA
    obtain ⟨hPpt, hPmv⟩ := hA
    rw [max_le_iff] at hB
    obtain ⟨hPnum, hC⟩ := hB
    rw [max_le_iff] at hC
    obtain ⟨hPexp, hD⟩ := hC
    rw [max_le_iff] at hD
    obtain ⟨hP8, hexpe⟩ := hD
    have hP1 : 1 ≤ P := by linarith
    have hPpos : 0 < P := by linarith
    have hN1 : 1 ≤ N := by linarith
    have hNpos : 0 < N := by linarith
    have hLpos : 0 < Real.log P := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log P := by
      have h1 : Real.exp 1 ≤ P := by linarith
      have h2 : Real.log (Real.exp 1) ≤ Real.log P := Real.log_le_log (Real.exp_pos 1) h1
      simpa using h2
    have hLNpos : 0 < Real.log N := Real.log_pos (by linarith)
    have hLN1 : 1 ≤ Real.log N := by
      have h1 : (3:ℝ) ≤ N := by exact_mod_cast hN
      have h2 : Real.exp 1 ≤ (3:ℝ) := by linarith [Real.exp_one_lt_d9]
      exact le_trans (by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h2)
        (Real.log_le_log (by norm_num) h1)
    have hC₀pos : 0 < C₀ := lt_of_lt_of_le (one_div_pos.mpr hLpos) hC₀
    haveI : NeZero q := ⟨by omega⟩
    obtain ⟨hn1, hn2, hn3⟩ := hnum P hPnum N C₀ q hN hNle hC₀ hq hqle
    have hexp1 : ∀ t : ℝ, |t| ≤ Real.pi * N / (2 * C₀) →
        |t| ≤ Real.exp (Real.log P ^ (21 / 20 : ℝ)) := by
      intro t ht
      have h2piN : 0 < 2 * Real.pi * N := by positivity
      have hξ : |t / (2 * Real.pi * N)| ≤ 1 / (4 * C₀) := by
        have h1 : |t| / (2 * Real.pi * N) ≤ (Real.pi * N / (2 * C₀)) / (2 * Real.pi * N) :=
          div_le_div_of_nonneg_right ht h2piN.le
        have h2' : (Real.pi * N / (2 * C₀)) / (2 * Real.pi * N) = 1 / (4 * C₀) := by
          field_simp
          ring
        rw [h2'] at h1
        rwa [abs_div, abs_of_pos h2piN]
      have h := hexp0 P N C₀ hPexp hN hNle hC₀ (t / (2 * Real.pi * N)) hξ
      have hx : 2 * Real.pi * N * (t / (2 * Real.pi * N)) = t := by
        field_simp
      rwa [hx] at h
    have hAge : ∀ t : ℝ, n4Eee C₁ c₁ P ≤ |t| →
        C₁ * pi0 P / (1 + |t|) ≤ Kc * n4Perr C₁ c₁ P q := by
      intro t ht
      have hEepos : 0 < n4Eee C₁ c₁ P := by rw [n4Eee]; positivity
      have hperrnn : 0 ≤ n4Perr C₁ c₁ P q := by rw [n4Perr]; positivity
      have h1 : n4Eee C₁ c₁ P ≤ 1 + |t| := by linarith [abs_nonneg t]
      have hpinonneg : 0 ≤ pi0 P := by rw [pi0]; positivity
      have h2 : C₁ * pi0 P / (1 + |t|) ≤ C₁ * pi0 P / n4Eee C₁ c₁ P :=
        div_le_div_of_nonneg_left (by positivity) hEepos h1
      have h3 : C₁ * pi0 P / n4Eee C₁ c₁ P
          = C₁ * (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ))) := by
        rw [n4Eee, pi0]
        field_simp
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h4 : C₁ * (C₁ * P * Real.exp (-c₁ * Real.log P ^ (1 / 12 : ℝ)))
          ≤ C₁ * n4Perr C₁ c₁ P q := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        rw [n4Perr]
        linarith [show 0 ≤ C₁ * (q.primeFactors.card : ℝ) by positivity]
      have h5 : C₁ * n4Perr C₁ c₁ P q ≤ Kc * n4Perr C₁ c₁ P q :=
        mul_le_mul_of_nonneg_right hKcC₁ hperrnn
      linarith [h2, h3, h4, h5]
    have hbrut := n4_integral_brut (ℓ := ℓ) (m := m) (P := P) (N := N) (C₀ := C₀) (q := q)
      (C₁ := C₁) (c₁ := c₁) (Cmv := Cmv) (Kc := Kc)
      hm hℓ2 hC₁ hc₁ hCmv hKc1 hKcC₁ hP1 hN hq hC₀pos hLpos hNpos hexp1
      (fun χ t ht => by
        have h := hpt P hPpt q (Classical.decEq _) hq hqle χ t ht
        by_cases hχ : χ = 1
        · simpa [if_pos hχ, n4Perr] using h
        · simpa [if_neg hχ, n4Perr] using h)
      (fun t ht => by
        have h := hAge t (by simpa [n4Eee] using ht)
        simpa [n4Perr, n4Eee] using h)
      (fun χ => by
        have h := hmv P hPmv q χ (Real.pi * N / (2 * C₀)) (by positivity)
        simpa using h)
    have har := harith P N C₀ q hN1 hLpos hLNpos hLN1 hL1 hP1 hq hC₀pos hn1 hn2 hn3
    exact le_trans hbrut har
  · refine ⟨1, 3, one_pos, ?_⟩
    intro P N C₀ q hP hN hNle hC₀ hq hqle
    exfalso
    have h1 : P ^ (ℓ - 1) = 1 := by
      rw [Nat.sub_eq_zero_of_le (by omega : ℓ ≤ 1), pow_zero]
    rw [h1] at hNle
    linarith [hN, hNle]


/-! ## 11. The numerical estimates (stub for testing) -/

/-! ## 11. The final theorem -/

theorem n4_case_small_q (ℓ m : ℕ) (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ → 1 ≤ q → q ≤ (Real.log P) ^ (ℓ + 4) →
      ((n4set ℓ m P N C₀ q).card : ℝ) ≤
        C * C₀ * pi0 P ^ (2 * ℓ) / N *
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N) := by
  by_cases hℓ2 : 2 ≤ ℓ
  · -- The four inputs of the conditional master theorem.
    obtain ⟨c, C, Pw, hc, hW⟩ := prime_char_sum_window ((ℓ + 4 : ℕ) : ℝ) (by positivity)
    obtain ⟨c₁, C₁, Pp, hc₁, hC₁, hPp, hpt0⟩ :=
      n4_psum_of_window ((ℓ + 4 : ℕ) : ℝ) (by positivity) hc hW
    obtain ⟨Knum, Pnum, hKnum, hPnum, hnum0⟩ := n4_numerics_small_q_12 ℓ hℓ2 c₁ C₁ hc₁ hC₁
    obtain ⟨Cmv, Pmv, hCmv, hmv0⟩ := n4_mv_bound ℓ hℓ
    obtain ⟨Pexp, hPexp, hexp0⟩ := n4_exp_range_aux ℓ
    refine n4_case_small_q_master ℓ m hℓ hm hc₁ hC₁ hCmv hKnum
      (le_max_right C₁ 1) (le_max_left C₁ 1)
      (Ppt := Pp) (Pmv := Pmv) (Pnum := Pnum) (Pexp := Pexp) ?_ ?_ ?_ ?_
    · -- the pointwise prime-character bound
      intro P hP q _dec hq hqle χ t ht
      haveI : NeZero q := ⟨by omega⟩
      have hqle' : (q : ℝ) ≤ Real.log P ^ (((ℓ + 4 : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hqle
      have h := hpt0 P hP q hqle' χ t ht
      by_cases hχ : χ = 1
      · rw [if_pos hχ] at h ⊢
        exact h
      · rw [if_neg hχ] at h ⊢
        exact h
    · -- the mean-value bound
      intro P hP q χ T hT
      simpa only [psum] using hmv0 P hP q χ T hT
    · -- the numerical comparisons
      intro P hP N C₀ q hN hNle hC₀ hq hqle
      exact hnum0 P N C₀ q hP hN hNle hC₀ hq hqle
    · -- the twist-range check
      exact ⟨Pexp, hPexp, hexp0⟩
  · -- `ℓ = 1`: the hypothesis `3 ≤ N ≤ P ^ (ℓ - 1) = 1` is contradictory.
    refine ⟨1, 2, one_pos, ?_⟩
    intro P N C₀ q hP hN hNle hC₀ hq hqle
    exfalso
    have h1 : P ^ (ℓ - 1) = 1 := by
      rw [Nat.sub_eq_zero_of_le (by omega : ℓ ≤ 1), pow_zero]
    rw [h1] at hNle
    linarith [hN, hNle]

end Work.BMF
