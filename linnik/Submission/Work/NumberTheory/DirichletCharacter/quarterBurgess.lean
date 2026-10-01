import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.Algebra.Group.orderOf_map_eq_of_injective
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree

open scoped BigOperators
open Finset MeasureTheory intervalIntegral

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

open scoped Classical in
/-- `χ.primitiveCharacter` and `χ` have the same order (the former induces the latter through the
injective `changeLevel` map). -/
theorem orderOf_primitiveCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    orderOf χ.primitiveCharacter = orderOf χ := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := Commons.Algebra.Group.orderOf_map_eq_of_injective
    (DirichletCharacter.changeLevel χ.conductor_dvd_level)
    (DirichletCharacter.changeLevel_injective χ.conductor_dvd_level) χ.primitiveCharacter
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  exact h.symm

theorem abel_exp_log {a : ℕ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (θ : ℝ) (hθ : 0 < θ)
    {s : ℂ} (hσ0 : 0 < s.re) (hσθ : θ ≤ s.re)
    {Q M : ℕ} (hQ : 1 ≤ Q) (hQM : Q + 1 ≤ M)
    (hPre : ∀ m : ℕ, Q ≤ m → m ≤ M →
        ‖∑ k ∈ Finset.Icc 1 m, a k‖ ≤ A * (m:ℝ)^(θ)) :
    ‖∑ k ∈ Finset.Icc (Q+1) M, a k * (k:ℂ)^(-s)‖
      ≤ A * (Q:ℝ)^(θ - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := by
  set w : ℕ → ℂ := fun n => (n:ℂ)^(-s) with hw
  have hnw : ∀ n : ℕ, 1 ≤ n → ‖w n‖ = (n:ℝ)^(-s.re) := by
    intro n hn; rw [hw]; exact norm_natCast_cpow_eq s hn
  have hdiff : ∀ n : ℕ, 1 ≤ n → ‖w n - w (n+1)‖ ≤ ‖s‖ * (n:ℝ)^(-(s.re+1)) := by
    intro n hn; rw [hw]; exact norm_cpow_nat_sub_succ_cpow_le s hσ0 hn
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 0 < Q)
  rw [Commons.Algebra.BigOperators.abel_window a w (by omega) hQM]
  have hMQ : (Q:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : Q ≤ M)
  -- term 1
  have hT1 : ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M‖
      ≤ A * (Q:ℝ)^(θ - s.re) := by
    have h1 := hPre M (by omega) le_rfl
    rw [norm_mul, hnw M (by omega)]
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    calc ‖∑ m ∈ Finset.Icc 1 M, a m‖ * (M:ℝ)^(-s.re)
        ≤ (A * (M:ℝ)^(θ)) * (M:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg M) _)
      _ = A * (M:ℝ)^(θ - s.re) := by
          rw [mul_assoc, ← Real.rpow_add hMpos]; simp only [sub_eq_add_neg]
      _ ≤ A * (Q:ℝ)^(θ - s.re) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQpos hMQ (by linarith)) hA
  -- term 2
  have hT2 : ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖
      ≤ A * (Q:ℝ)^(θ - s.re) := by
    rw [show (Q+1-1 : ℕ) = Q by omega, norm_mul, hnw (Q+1) (by omega)]
    have h1 := hPre Q le_rfl (by omega)
    have hstep : ((Q+1:ℕ):ℝ)^(-s.re) ≤ (Q:ℝ)^(-s.re) :=
      Real.rpow_le_rpow_of_nonpos hQpos (by exact_mod_cast (by omega : Q ≤ Q+1)) (by linarith)
    calc ‖∑ m ∈ Finset.Icc 1 Q, a m‖ * ((Q+1:ℕ):ℝ)^(-s.re)
        ≤ (A * (Q:ℝ)^(θ)) * ((Q+1:ℕ):ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _)
      _ ≤ (A * (Q:ℝ)^(θ)) * (Q:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = A * (Q:ℝ)^(θ - s.re) := by
          rw [mul_assoc, ← Real.rpow_add hQpos]; simp only [sub_eq_add_neg]
  -- term 3
  have hT3 : ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
        (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖
      ≤ A * ‖s‖ * (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)) := by
    calc ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
            (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖
        ≤ ∑ n ∈ Finset.Icc (Q+1) (M-1),
            ‖(∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (Q+1) (M-1),
            (A * (n:ℝ)^(θ)) * (‖s‖ * (n:ℝ)^(-(s.re+1))) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          rw [norm_mul]
          exact mul_le_mul (hPre n (by omega) (by omega)) (hdiff n (by omega))
            (norm_nonneg _) (by positivity)
      _ = ∑ n ∈ Finset.Icc (Q+1) (M-1), A * ‖s‖ * (n:ℝ)^(θ - (s.re+1)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
          rw [show (A * (n:ℝ)^(θ)) * (‖s‖ * (n:ℝ)^(-(s.re+1)))
              = A * ‖s‖ * ((n:ℝ)^(θ) * (n:ℝ)^(-(s.re+1))) by ring,
            ← Real.rpow_add hnpos]
          simp only [sub_eq_add_neg, neg_add_rev]
      _ = ∑ n ∈ Finset.Ioc Q (M-1), A * ‖s‖ * (n:ℝ)^(θ - (s.re+1)) := by
          rw [show Finset.Icc (Q+1) (M-1) = Finset.Ioc Q (M-1) from by
            ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
      _ ≤ A * ‖s‖ * (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)) := by
          have hsum_eq : ∑ n ∈ Finset.Ioc Q (M-1), A * ‖s‖ * (n:ℝ)^(θ - (s.re+1))
              = A * ‖s‖ * (∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^(θ - s.re - 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro n hn
            rw [show θ - (s.re+1) = θ - s.re - 1 by ring]
          rw [hsum_eq]
          have hsplit : ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^(θ - s.re - 1)
              ≤ ∑ n ∈ Finset.Ioc Q (M-1), (Q:ℝ)^(θ - s.re) * (n:ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Ioc] at hn
            have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
            have hle : (n:ℝ)^(θ - s.re) ≤ (Q:ℝ)^(θ - s.re) :=
              Real.rpow_le_rpow_of_nonpos hQpos (by exact_mod_cast (by omega : Q ≤ n)) (by linarith)
            rw [show (n:ℝ)^(θ - s.re - 1) = (n:ℝ)^(θ - s.re) * (n:ℝ)⁻¹ by
              rw [← Real.rpow_neg_one]; rw [← Real.rpow_add hnpos]; ring_nf]
            exact mul_le_mul_of_nonneg_right hle (by positivity)
          have hsum_inv : ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)⁻¹ ≤ 1 + Real.log (M:ℝ) := by
            refine (sum_Ioc_inv_le_log (Q := Q) (M := M-1)).trans ?_
            have hle : Real.log ((M-1:ℕ):ℝ) ≤ Real.log (M:ℝ) :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < M - 1))
                (by exact_mod_cast (by omega : M - 1 ≤ M))
            exact add_le_add le_rfl hle
          calc A * ‖s‖ * (∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^(θ - s.re - 1))
              ≤ A * ‖s‖ * ((Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                calc ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^(θ - s.re - 1)
                    ≤ ∑ n ∈ Finset.Ioc Q (M-1), (Q:ℝ)^(θ - s.re) * (n:ℝ)⁻¹ := hsplit
                  _ = (Q:ℝ)^(θ - s.re) * ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)⁻¹ := by
                      rw [Finset.mul_sum]
                  _ ≤ (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)) :=
                      mul_le_mul_of_nonneg_left hsum_inv (Real.rpow_nonneg (le_of_lt hQpos) _)
            _ = A * ‖s‖ * (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)) := by ring
  have hfin : (A * (Q:ℝ)^(θ - s.re)
        + A * ‖s‖ * (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)))
        + A * (Q:ℝ)^(θ - s.re)
      = A * (Q:ℝ)^(θ - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := by ring
  calc ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M
          + (∑ n ∈ Finset.Icc (Q+1) (M-1), (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1)))
          - (∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖
      ≤ ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M
          + (∑ n ∈ Finset.Icc (Q+1) (M-1), (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1)))‖
        + ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖ := norm_sub_le _ _
    _ ≤ (‖(∑ m ∈ Finset.Icc 1 M, a m) * w M‖
          + ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
              (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖)
        + ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (A * (Q:ℝ)^(θ - s.re)
          + A * ‖s‖ * (Q:ℝ)^(θ - s.re) * (1 + Real.log (M:ℝ)))
        + A * (Q:ℝ)^(θ - s.re) :=
          add_le_add (add_le_add hT1 hT3) hT2
    _ = A * (Q:ℝ)^(θ - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := hfin

theorem primitive_LFunction_bound_quarter (k : ℕ) (hk : 3 ≤ k) (M : ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε/4)
    {CB : ℝ} (hCB : 0 < CB) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → orderOf χ ≤ M →
        (∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
          ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ CB * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (H:ℝ)^((1 - 1/((k:ℝ))))) →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ)+(t:ℂ)*Complex.I)‖
            ≤ C * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1 + |t|) := by
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hthnn : (0:ℝ) ≤ 1 - 1/(k:ℝ) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ))]
    linarith [hkR]
  obtain ⟨Clog, hClogpos, hClog⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < ε/2 by positivity) 1
  obtain ⟨Clog2, hClog2pos, hClog2⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < ε/8 by positivity) 1
  obtain ⟨CPV, hCPVpos, hCPV⟩ := Commons.NumberTheory.DirichletCharacter.polya_vinogradov
  have hC1pos : (0:ℝ) < 1 + Clog := by linarith
  have hC2pos : (0:ℝ) < 1 + Clog2 := by linarith
  have hCpos : (0:ℝ) < 3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h1 : (0:ℝ) < 1 + Clog := by linarith
    have h2 : (0:ℝ) < 1 + Clog2 := by linarith
    have h3 : (0:ℝ) < CB + 1 := by linarith
    positivity
  refine ⟨3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1, hCpos, ?_⟩
  intro q _inst χ hprim hχ _hord hB σ t hσ1 hσle
  have hq2 : 2 ≤ q := by
    by_contra h
    rcases (by omega : q = 0 ∨ q = 1) with h0 | h1
    · exact NeZero.ne q h0
    · exact hχ (DirichletCharacter.level_one' (χ := χ) h1)
  set θ : ℝ := ((k:ℝ)+1)/(4*(k:ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθle : θ ≤ 1/2 := by
    rw [hθdef, div_le_iff₀ (by positivity : (0:ℝ) < 4*(k:ℝ))]
    linarith [hkR]
  have hθlt1 : θ ≤ 1 := by linarith
  set μ : ℝ := 1 - σ with hμdef
  have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
  have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) hkR
  set Q : ℕ := Nat.ceil ((q:ℝ)^θ) with hQdef
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqRpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le one_pos hqR1
  have hQge : (q:ℝ)^θ ≤ (Q:ℝ) := Nat.le_ceil _
  have hqpow1 : (1:ℝ) ≤ (q:ℝ)^θ := Real.one_le_rpow hqR1 (le_of_lt hθpos)
  have hQ1 : 1 ≤ Q := by
    have : (1:ℝ) ≤ (Q:ℝ) := le_trans hqpow1 hQge
    exact_mod_cast this
  have hQq : Q ≤ q := by
    rw [hQdef]
    refine Nat.ceil_le.mpr ?_
    have := Real.rpow_le_rpow_of_exponent_le hqR1 hθlt1
    rwa [Real.rpow_one] at this
  have hQle : (Q:ℝ) ≤ 2*(q:ℝ)^θ := by
    have h := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hqRpos θ))
    linarith [h, hqpow1]
  -- prefix bound
  set A : ℝ := (CB+1) * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hPre : ∀ m : ℕ, 1 ≤ m → m ≤ q →
      ‖∑ n ∈ Finset.Icc 1 m, χ n‖ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
    intro m hm1 hmq
    rcases Nat.lt_or_ge 1 m with hm2 | hm2
    · have hmem : Finset.Icc 1 m = insert 1 (Finset.Ioc 1 m) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
      have hnotin : (1:ℕ) ∉ Finset.Ioc 1 m := by simp [Finset.mem_Ioc]
      rw [hmem, Finset.sum_insert hnotin]
      have hb := hB (N:=1) (H:=m-1) le_rfl (by omega) (by omega)
      rw [show (1:ℕ)+(m-1) = m by omega] at hb
      have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hm23 : (1:ℝ) ≤ (m:ℝ)^((1 - 1/((k:ℝ)))) := Real.one_le_rpow hmR hthnn
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hA1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
        have h1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.one_le_rpow hqR1 (by positivity)
        have := mul_le_mul h1 hm23 (by norm_num) (Real.rpow_nonneg (le_of_lt hqRpos) _)
        simpa using this
      have hfin : 1 + CB * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
        rw [hAdef]
        have hqnn : (0:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.rpow_nonneg (le_of_lt hqRpos) _
        nlinarith [hA1, hqnn, Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)) ((1 - 1/((k:ℝ)))), hCB.le]
      calc ‖χ ((1:ℕ):ZMod q) + ∑ n ∈ Finset.Ioc 1 m, χ n‖
          ≤ 1 + CB * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * ((m-1:ℕ):ℝ)^((1 - 1/((k:ℝ)))) := by
            refine (norm_add_le _ _).trans ?_
            exact add_le_add hχ1 hb
        _ ≤ 1 + CB * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (m:ℝ)^((1 - 1/((k:ℝ)))) := by
            have hHm : ((m-1:ℕ):ℝ)^((1 - 1/((k:ℝ)))) ≤ (m:ℝ)^((1 - 1/((k:ℝ)))) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : m-1 ≤ m)) hthnn
            have hh := mul_le_mul_of_nonneg_left hHm (by positivity : (0:ℝ) ≤ CB * (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2))
            linarith [hh]
        _ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) := hfin
    · have hm1' : m = 1 := by omega
      subst hm1'
      have hmem : Finset.Icc 1 1 = {1} := by ext n; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
      rw [hmem, Finset.sum_singleton]
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      refine hχ1.trans ?_
      rw [show (((1:ℕ):ℝ))^((1 - 1/((k:ℝ)))) = 1 by simp]
      rw [mul_one, hAdef]
      have h1 : (1:ℝ) ≤ (q:ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := Real.one_le_rpow hqR1 (by positivity)
      have h2 : (1:ℝ) ≤ CB + 1 := by linarith
      nlinarith [h1, h2, mul_le_mul h1 (le_refl (1:ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hqRpos) _)]
  -- s
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hsnorm : ‖s‖ ≤ 2 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre] at h
    have h1 : |s.im| = |t| := by simp [hsdef]
    have h2 : |σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; exact hσle
    rw [h1] at h; linarith
  -- head
  have hQpow : (Q:ℝ)^μ ≤ 2*(q:ℝ)^(θ*μ) := by
    have h1 : (Q:ℝ)^μ ≤ (2*(q:ℝ)^θ)^μ := Real.rpow_le_rpow (by positivity) hQle hμ0
    have h2 : (2*(q:ℝ)^θ)^μ = 2^μ * (q:ℝ)^(θ*μ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (le_of_lt hqRpos)]
    have h3 : (2:ℝ)^μ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (show μ ≤ 1 by linarith)
      simpa using this
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by positivity) _))
  have hQlog : 1 + Real.log (Q:ℝ) ≤ (1+Clog) * (q:ℝ)^(ε/2) := by
    have h1 : Real.log (Q:ℝ) ≤ Clog * (Q:ℝ)^(ε/2) := by
      simpa using hClog (Q:ℝ) (by exact_mod_cast hQ1)
    have h2 : (Q:ℝ)^(ε/2) ≤ (q:ℝ)^(ε/2) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQq) (by positivity)
    have h3 : (1:ℝ) ≤ (q:ℝ)^(ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have h4 : Real.log (Q:ℝ) ≤ Clog * (q:ℝ)^(ε/2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hClogpos))
    nlinarith [h3, h4]
  have hhead : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    have h1 := sum_Icc_one_rpow_le hQ1 hμ0
    have hQμ1 : (1:ℝ) ≤ (Q:ℝ)^μ := Real.one_le_rpow (by exact_mod_cast hQ1) hμ0
    have hqexp : (1:ℝ) ≤ (q:ℝ)^(θ*μ + ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have hpw : (q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2) = (q:ℝ)^(θ*μ+ε/2) := (Real.rpow_add hqRpos _ _).symm
    calc ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ)
        = ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(μ-1) := by
          apply Finset.sum_congr rfl; intro n hn; congr 1; rw [hμdef]; ring
      _ ≤ 1 + (Q:ℝ)^μ * (1 + Real.log (Q:ℝ)) := h1
      _ ≤ 1 + (2*(q:ℝ)^(θ*μ)) * ((1+Clog) * (q:ℝ)^(ε/2)) := by
          apply add_le_add le_rfl
          exact mul_le_mul hQpow hQlog (by positivity) (by positivity)
      _ = 1 + 2*(1+Clog) * ((q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2)) := by ring
      _ = 1 + 2*(1+Clog) * (q:ℝ)^(θ*μ+ε/2) := by rw [hpw]
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
          have hqnn : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg (le_of_lt hqRpos) _
          have hClognn : (0:ℝ) ≤ Clog := le_of_lt hClogpos
          nlinarith [hqexp, hqnn, hClognn, mul_le_mul_of_nonneg_left hqexp hClognn]
  -- Chead
  have hhead2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ 3*(1+Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    refine hhead.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hqRpos) _)
    linarith [hClogpos]
  have hqn1 : (0:ℝ) ≤ (q:ℝ) := le_of_lt hqRpos
  have hσeq : σ = 1 - μ := by rw [hμdef]; ring
  have hslack1 : θ*μ + ε/2 ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
    have hkey : θ*μ = μ*(1+1/(k:ℝ))/4 := by
      rw [hθdef]; field_simp; try ring
    rw [hkey]
    linarith [hδε, hδ, hε]
  have hhead3 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    have h1 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum; intro n hn
      rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
    have h2 : (3+2*Clog) * (q:ℝ)^(θ*μ+ε/2) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) := by
      have hx : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg hqn1 _
      have hcoef : (3+2*Clog) ≤ 3*(1+Clog) := by linarith [hClogpos]
      have hrhs : (0:ℝ) ≤ 3*(1+Clog) := by linarith [hClogpos]
      exact mul_le_mul hcoef hqle1 hx hrhs
    have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
    calc ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := h1
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := hhead
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) := h2
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
  have hσ23 : (1 - 1/((k:ℝ))) ≤ s.re := by rw [hsre]; linarith [hσ1, hkR]
  have hδ' : (0:ℝ) < (ε/8) := by positivity
  -- middle bound
  have hmid : ∀ R : ℕ, Q+1 ≤ R → R ≤ q →
      ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro R hQR hRq
    have hPreR : ∀ m : ℕ, Q ≤ m → m ≤ R → ‖∑ k ∈ Finset.Icc 1 m, χ k‖ ≤ A * (m:ℝ)^((1 - 1/((k:ℝ)))) :=
      fun m hm1 hm2 => hPre m (by omega) (by omega)
    have hh := abel_exp_log (le_of_lt hApos) (1 - 1/((k:ℝ))) (by linarith [hkR]) hs0
      (by rw [hsre]; exact hσ1) hQ1 hQR
      (a := fun n => χ n) hPreR
    have hQpow : (Q:ℝ)^((1 - 1/((k:ℝ))) - s.re) ≤ (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) := by
      rw [hsre]
      have hle := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hqRpos θ) hQge
        (show (1 - 1/((k:ℝ))) - σ ≤ 0 by linarith [hσ23])
      rwa [← Real.rpow_mul hqn1] at hle
    have hlogR : (1:ℝ) + Real.log (R:ℝ) ≤ (1+Clog2) * (q:ℝ)^((ε/8)) := by
      have h1 : Real.log (R:ℝ) ≤ Clog2 * (R:ℝ)^((ε/8)) := by
        simpa using hClog2 (R:ℝ) (by exact_mod_cast (by omega : 1 ≤ R))
      have h2 : (R:ℝ)^((ε/8)) ≤ (q:ℝ)^((ε/8)) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hRq) (by positivity)
      have h3 : (1:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      have h4 : Real.log (R:ℝ) ≤ Clog2 * (q:ℝ)^((ε/8)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (le_of_lt hClog2pos))
      nlinarith [h3, h4, hClog2pos, Real.rpow_nonneg hqn1 ((ε/8))]
    have hY1 : (1:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by
      have h3 : (1:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      nlinarith [h3, hClog2pos]
    have hY0 : (0:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by positivity
    have hsn' : ‖s‖ ≤ 2*(1+|t|) := by linarith [hsnorm, abs_nonneg t]
    have hYbound : (2:ℝ) + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8)))
        ≤ 4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|) := by
      have h4 : ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))) ≤ 2*(1+|t|)*((1+Clog2)*(q:ℝ)^((ε/8))) :=
        mul_le_mul_of_nonneg_right hsn' hY0
      have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
      have hY2 : (0:ℝ) ≤ (q:ℝ)^((ε/8)) := Real.rpow_nonneg hqn1 _
      nlinarith [h4, hY1, hY0, ht1, hsn', hClog2pos, hY2, le_of_lt hδ']
    have hE : ((((k:ℝ)+1)/(4*((k:ℝ))^2)) + ε/2) + θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)
        ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
      have hkey : ((((k:ℝ)+1)/(4*((k:ℝ))^2))) + θ*((1 - 1/((k:ℝ))) - σ) = μ*(1+1/(k:ℝ))/4 := by
        rw [hσeq, hθdef]; field_simp; ring
      linarith [hkey, hδε, hδ, hε]
    have hcomb : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ))
        = (CB+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) := by
      rw [hAdef, mul_assoc, ← Real.rpow_add hqRpos]
    have hrr : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|))
        = (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|))
          = (CB+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|)) := by
            rw [hcomb]
        _ = (CB+1) * ((q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ)) * (q:ℝ)^((ε/8))) * (4*(1+Clog2)*(1+|t|)) := by ring
        _ = (CB+1) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ) + (ε/8)) * (4*(1+Clog2)*(1+|t|)) := by
            rw [← Real.rpow_add hqRpos]
        _ = (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ)))-σ) + (ε/8)) * (1+|t|) := by ring
    have hstep : A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))))
        ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8))))
          ≤ A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (4*(1+Clog2)*(q:ℝ)^((ε/8))*(1+|t|)) :=
            mul_le_mul le_rfl hYbound (by positivity) (by positivity)
        _ = _ := hrr
    calc ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ A * (Q:ℝ)^((1 - 1/((k:ℝ))) - s.re) * (2 + ‖s‖*(1+Real.log (R:ℝ))) := hh
      _ ≤ A * (q:ℝ)^(θ*((1 - 1/((k:ℝ))) - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^((ε/8)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQpow (le_of_lt hApos))
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogR (norm_nonneg s))) (by positivity) (by positivity)
      _ ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)+θ*((1 - 1/((k:ℝ))) - σ) + (ε/8)) * (1+|t|) := hstep
      _ ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          have hq2 := Real.rpow_le_rpow_of_exponent_le hqR1 hE
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 (by positivity)) (by positivity)
  -- tail bound
  have hPV : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, χ n‖ ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
    intro x y hxy
    have h1 : ‖∑ n ∈ Finset.range (y+1), χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := hCPV q hq2 χ hχ y
    have h2 : ‖∑ n ∈ Finset.range x, χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp; positivity
      · have h := hCPV q hq2 χ hχ (x-1)
        rwa [show x-1+1 = x by omega] at h
    have hsplit : ∑ n ∈ Finset.Icc x y, χ n = (∑ n ∈ Finset.range (y+1), χ n) - ∑ n ∈ Finset.range x, χ n := by
      have hun : Finset.range (y+1) = Finset.range x ∪ Finset.Icc x y := by
        ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.range x) (Finset.Icc x y) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Icc] at h2; omega
      rw [hun, Finset.sum_union hdisj]; ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith [h1, h2])
  have hlogqq : Real.log (q:ℝ) ≤ (1+Clog2)*(q:ℝ)^((ε/8)) := by
    have h1 : Real.log (q:ℝ) ≤ Clog2 * (q:ℝ)^((ε/8)) := by simpa using hClog2 (q:ℝ) hqR1
    nlinarith [h1, hClog2pos, Real.rpow_nonneg hqn1 ((ε/8))]
  have hσinv : (1:ℝ) + ‖s‖/σ ≤ 4*(1+|t|) := by
    have h2 : ‖s‖/s.re ≤ (2+|t|)/(2/3) :=
      div_le_div₀ (by positivity) hsnorm (by norm_num) (by linarith [hσ23])
    rw [hsre] at h2
    nlinarith [h2, hsnorm, abs_nonneg t]
  have htail : ∀ M : ℕ, q < M →
      ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro M hqM
    have hh := Commons.Analysis.Asymptotics.abel_tail_bound_finite
      (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) hPV s hs0 (N := q+1) (M := M) (by omega) (by omega)
    have hBnn : (0:ℝ) ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
      positivity
    have hstep0 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re)
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hqRpos (by exact_mod_cast (by omega : q ≤ q+1)) (by rw [hsre]; linarith [hs0])) hBnn
    have hexp_t : (1:ℝ)/2 - σ + (ε/8) ≤ μ*(1+1/(k:ℝ))/4 + ε - δ := by
      have h1 : (1:ℝ)/2 - σ ≤ -1/6 := by linarith [h1k, hσ1]
      have h3 : (0:ℝ) ≤ μ*(1+1/(k:ℝ))/4 := by positivity
      have h4 : ε/2 ≤ ε - δ := by linarith [hδε]
      linarith [h1, h3, h4, hδ, hε]
    have hq3 : (q:ℝ)^((1:ℝ)/2 - σ + (ε/8)) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hexp_t
    have hstep1 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re)
        ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := by
      rw [hsre, Real.sqrt_eq_rpow]
      have hAq : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8))) :=
        mul_le_mul_of_nonneg_left hlogqq (by positivity)
      have h5 : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ) :=
        mul_le_mul_of_nonneg_right hAq (Real.rpow_nonneg hqn1 _)
      have h6 : (0:ℝ) ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ) := by positivity
      have h7 := mul_le_mul h5 hσinv (by
        have hσpos : (0:ℝ) < σ := by linarith [hσ23]
        positivity) h6
      have hrr : (q:ℝ)^((1:ℝ)/2) * (q:ℝ)^((ε/8)) * (q:ℝ)^(-σ)
          = (q:ℝ)^((1:ℝ)/2 - σ + (ε/8)) := by
        rw [← Real.rpow_add hqRpos, ← Real.rpow_add hqRpos]
        congr 1; ring
      calc 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)*(1+‖s‖/σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^((ε/8)))*(q:ℝ)^(-σ)*(4*(1+|t|)) := h7
        _ = 8*CPV*(1+Clog2)*((q:ℝ)^((1:ℝ)/2)*(q:ℝ)^((ε/8))*(q:ℝ)^(-σ))*(1+|t|) := by ring
        _ = 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := by rw [hrr]
    calc ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re) * (1+‖s‖/s.re) := hh
      _ ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re) :=
          mul_le_mul_of_nonneg_right hstep0 (by positivity)
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + (ε/8))*(1+|t|) := hstep1
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq3 (by positivity)) (by positivity)
      _ ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
          have h5 : (8:ℝ)*CPV*(1+Clog2) ≤ 14*CPV*(1+Clog2) := by
            nlinarith [hCPVpos, hClog2pos]
          calc 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)
              = (8*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)) := by ring
            _ ≤ (14*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)*(1+|t|)) :=
                mul_le_mul_of_nonneg_right h5 h4
            _ = (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by ring
  -- per-M bound
  have hBig : (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
      ≤ 3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h4 : (0:ℝ) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by positivity
    linarith
  have hPerM : ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
          * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
    intro M
    have hTpos : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
    by_cases hMQ : M ≤ Q
    · have h1 : ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ n ∈ Finset.Icc 1 M, ‖χ n * (n:ℂ)^(-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 M, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum; intro n hn
              rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
              exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
          _ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
              · intro n hn _; positivity
      have h2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) := by
        refine hhead2.trans ?_
        have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4+ε-δ) :=
          Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
        exact mul_le_mul_of_nonneg_left hqle1 (by positivity)
      refine (h1.trans h2).trans ?_
      have hk1 : (3*(1+Clog)) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by
        have h2 : (0:ℝ) ≤ 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by positivity
        linarith
      calc (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ)
          ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) :=
            mul_le_mul_of_nonneg_right hk1 (Real.rpow_nonneg hqn1 _)
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
            have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
            rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
    · have hMQ' : Q ≤ M := le_of_lt (lt_of_not_ge hMQ)
      have hsplit1 : ∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s) + ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s) :=
        sum_Icc_split hMQ' _
      rw [hsplit1]
      have hQR : Q ≤ min M q := le_min hMQ' hQq
      have hRM : min M q ≤ M := min_le_left _ _
      have hsplit2 : ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)
            + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) :=
        sum_Ioc_split hQR hRM _
      rw [hsplit2]
      have hmid' : ‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
          ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge Q (min M q) with hQR' | hQR'
        · have hIcc : Finset.Ioc Q (min M q) = Finset.Icc (Q+1) (min M q) := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact hmid (min M q) (by omega) (min_le_right _ _)
        · have hz : ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      have htail' : ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖
          ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge (min M q) M with hRM' | hRM'
        · have hRq : min M q = q := by omega
          rw [hRq] at hRM'
          rw [hRq]
          have hIcc : Finset.Ioc q M = Finset.Icc (q+1) M := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact htail M hRM'
        · have hz : ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      calc ‖(∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s))
            + ((∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s))‖
          ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + ‖(∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖ := norm_add_le _ _
        _ ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + (‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
              + ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖) :=
              add_le_add le_rfl (norm_add_le _ _)
        _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)
            + ((4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)
              + (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|)) :=
              add_le_add hhead3 (add_le_add hmid' htail')
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by
              nlinarith [hTpos, hClogpos, hClog2pos, hCPVpos]
  have hlim := LSeries_partial_sums_tendsto χ hχ hs0
  have hnormlim : Filter.Tendsto (fun M : ℕ => ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖)
      Filter.atTop (nhds ‖χ.LFunction s‖) := hlim.norm
  have hfin := le_of_tendsto' hnormlim hPerM
  rw [show ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ = μ*(1+1/(k:ℝ))/4 + ε - δ by
    rw [hμdef]; ring]
  refine hfin.trans ?_
  have h4 : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/4 + ε - δ) * (1+|t|) := by positivity
  nlinarith [h4, mul_le_mul_of_nonneg_right hBig h4]

set_option maxHeartbeats 2000000
lemma crude_absorb_quarter {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ q : ℕ, 1 ≤ q → ∀ σ : ℝ, 1 ≤ σ →
      σ ≤ 1 + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) →
      (1 + Real.log (q:ℝ)) ≤ Cf * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
  obtain ⟨Cl, hClpos, hCl⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow hε 3
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  refine ⟨8*(1+Cl) + 8, by positivity, ?_⟩
  intro q hq1 σ hσge hσle
  rcases eq_or_lt_of_le hq1 with hq | hq
  · subst hq
    simp only [Nat.cast_one, Real.log_one, Real.one_rpow, mul_one]
    nlinarith [hClpos]
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (le_of_lt hq)
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
  have hlogqpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hqe1 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hqR1 (le_of_lt hε)
  set e : ℝ := (1:ℝ)/4 + 1/(4*(k:ℝ)) with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hee : (1+1/(k:ℝ))/4 = e := by rw [hedef]; ring
  have hsq : (1 + Real.log (q:ℝ))^3 ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    have h1 : (Real.log (q:ℝ))^3 ≤ Cl * (q:ℝ)^ε := hCl (q:ℝ) hqR1
    have h2 : (1:ℝ) ≤ 1 + Real.log (q:ℝ) := by linarith
    have h3 : (1 + Real.log (q:ℝ))^3 = 1 + 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 + (Real.log (q:ℝ))^3 := by ring
    have h4 : 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 ≤ 3 + 6*(Real.log (q:ℝ))^2 := by
      nlinarith [hlogq0, h2, pow_nonneg hlogq0 2, sq_nonneg (Real.log (q:ℝ) - 1)]
    nlinarith [h1, h4, hlogq0, hqe1, hClpos, Real.rpow_nonneg (by positivity) ε, pow_nonneg hlogq0 2]
  have hloge : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^(2:ℕ) := by
    have h1 : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^e :=
      Real.rpow_le_rpow hlogq0 (by linarith) (le_of_lt hepos)
    have h2 : e ≤ 2 := by
      rw [hedef]
      have h : (4:ℝ) ≤ 4*(k:ℝ) := by linarith [hkR]
      have h3 : 1/(4*(k:ℝ)) ≤ 1/4 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) h
      linarith
    have h3 : (1 + Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^((2:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Real.log_nonneg hqR1)) h2
    exact h1.trans (by simpa only [Real.rpow_natCast] using h3)
  have hprod : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ (1 + Real.log (q:ℝ)) * (1 + Real.log (q:ℝ))^2 :=
          mul_le_mul_of_nonneg_left hloge (by linarith)
      _ = (1 + Real.log (q:ℝ))^3 := by ring
      _ ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hsq
  set L : ℝ := Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) with hLdef
  have hexp_eq : Real.log (q:ℝ) = (q:ℝ)^L := by
    rw [hLdef, Real.rpow_def_of_pos hqRpos]
    rw [show Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ))/Real.log (q:ℝ)) = Real.log (Real.log (q:ℝ)) by field_simp]
    exact (Real.exp_log hlogqpos).symm
  have hlogeq : (q:ℝ)^(e * L) = (Real.log (q:ℝ))^e := by
    conv_rhs => rw [hexp_eq, ← Real.rpow_mul (le_of_lt hqRpos)]
    rw [mul_comm]
  have hqe : (q:ℝ)^ε ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (Real.log (q:ℝ))^e := by
    rw [← hlogeq, ← Real.rpow_add hqRpos]
    apply Real.rpow_le_rpow_of_exponent_le hqR1
    have h1 : (1:ℝ) - σ + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) ≥ 0 := by linarith [hσle]
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1+1/(k:ℝ) by positivity)
    rw [← hee]
    nlinarith [h2]
  have hloge_pos : 0 < (Real.log (q:ℝ))^e := Real.rpow_pos_of_pos hlogqpos e
  have hfinal : (1 + Real.log (q:ℝ)) ≤ (8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
    have h1 : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (Real.log (q:ℝ))^e := by
      calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
          ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hprod
        _ ≤ (8*(1+Cl)+8) * ((q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (Real.log (q:ℝ))^e) :=
            mul_le_mul_of_nonneg_left hqe (by positivity)
        _ = ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (Real.log (q:ℝ))^e := by ring
    exact le_of_mul_le_mul_right h1 hloge_pos
  exact hfinal




theorem LFunction_bound_quarter_of_burgess {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k) (M : ℕ)
    {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      orderOf χ ≤ M →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          CB * (q : ℝ) ^ ((((k:ℝ)+1)/(4*((k:ℝ))^2)) + ε/2) * (H : ℝ) ^ (1 - 1/((k:ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      orderOf χ ≤ M →
      ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  set δ : ℝ := ε/4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδε : δ ≤ ε/4 := le_rfl
  obtain ⟨Cp, hCppos, hCp⟩ := primitive_LFunction_bound_quarter k hk M hε hδ hδε hCB
  obtain ⟨Cpd, hCpdpos, hCpd⟩ := prod_primeFactors_one_add_rpow_le' (by norm_num : (1/2:ℝ) ≤ 1/2) hδ
  obtain ⟨Cc, hCcpos, hCc⟩ := LFunction_crude_bound
  obtain ⟨Cf, hCfpos, hCf⟩ := crude_absorb_quarter hk hε
  refine ⟨max (Cp * Cpd) (Cc * Cf) + 1, by positivity, ?_⟩
  intro q _inst χ hχ hord σ t hσ hσle
  have hσ12 : (1:ℝ)/2 ≤ σ := by
    have h3k : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) h3k
    linarith
  by_cases hσ1 : σ ≤ 1
  · have hχprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hχprim_ne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ hχ
    have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hord' : orderOf χ.primitiveCharacter ≤ M := by
      rw [orderOf_primitiveCharacter]; exact hord
    have hB' : ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ χ.conductor →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ.primitiveCharacter n‖ ≤
          CB * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (H:ℝ)^(1 - 1/((k:ℝ))) := by
      intro N H hN hH hHq
      exact hB (q := χ.conductor) (χ := χ.primitiveCharacter) hχprim hχprim_ne hord' hN hH hHq
    have hpb := hCp χ.conductor χ.primitiveCharacter hχprim hχprim_ne hord' hB' σ t hσ hσ1
    have hred := LFunction_nonprimitive_le χ hχ (σ := σ) hσ12 (t := t)
    have hprod_le : (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ))) ≤ Cpd * (q:ℝ)^δ := by
      refine (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_).trans (hCpd q (NeZero.ne q))
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1/2:ℝ) by linarith)
      linarith
    have hE0 : 0 ≤ ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ := by
      have : (0:ℝ) ≤ (1-σ)*(1+1/(k:ℝ))/4 := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
      linarith [hδε, hε]
    have hqstar : (χ.conductor : ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ)
        ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
      · exact hE0
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)))
            * ‖@DirichletCharacter.LFunction χ.conductor hcond χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ := hred
      _ ≤ (Cpd * (q:ℝ)^δ) * (Cp * (χ.conductor:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1+|t|)) := by
          apply mul_le_mul hprod_le hpb (norm_nonneg _) (by positivity)
      _ = (Cp * Cpd) * ((χ.conductor:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by ring
      _ ≤ (Cp * Cpd) * ((q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by
          have h2 : (0:ℝ) ≤ (q:ℝ)^δ := Real.rpow_nonneg (by positivity) _
          have h3 : (0:ℝ) ≤ (1+|t|) := by positivity
          have h4 := mul_le_mul_of_nonneg_right hqstar h2
          have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ Cp*Cpd*(1+|t|))
          linarith [h5]
      _ = (Cp * Cpd) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          rw [← Real.rpow_add (by exact_mod_cast (NeZero.pos q) : (0:ℝ) < (q:ℝ))]
          rw [show ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ + δ = ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε by ring]
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cp * Cpd ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_left (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCppos, hCpdpos]
  · have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcb := hCc q χ hχ σ t hσge
    have hca := hCf q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) σ hσge hσle
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ Cc * (1 + Real.log (q:ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (1 + |t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos)
      _ = (Cc * Cf) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by ring
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cc * Cf ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_right (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCcpos, hCfpos]



/-- **HB Lemma 2.5 with φ = 1/4 at bounded order.**  From the cube-free Burgess character-sum
input one gets, for characters of order at most the fixed number `M` (e.g. `M = 2` for real
characters), the bound `L(σ+it,χ) ≪ q^{(1/4)(1-σ)(1+1/k)+ε}(1+|t|)`.

The order factor `(orderOf χ)^{3/(2k)}` produced by `burgess_charSum_order_of_cubefree` is
absorbed into the constant because `orderOf χ ≤ M` is fixed. -/
theorem LFunction_bound_quarter_of_bounded_order {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k)
    (M : ℕ) (hM : 1 ≤ M) {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
        (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
        ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
          ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖
            ≤ CB * (u : ℝ) ^ ((((k:ℝ)+1)/(4*((k:ℝ))^2)) + ε/4)
                * (H : ℝ) ^ (1 - 1/((k:ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → orderOf χ ≤ M →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
          ≤ C * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  set δ : ℝ := ε/4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδε : δ ≤ ε/4 := le_rfl
  obtain ⟨Co, hCopos, hCo⟩ :=
    burgess_charSum_order_of_cubefree (show (0:ℝ) < ε/4 by positivity) k (by omega) hCB hB
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  set CB' : ℝ := Co * (M:ℝ)^((3:ℝ)/(2*(k:ℝ))) + 1 with hCB'def
  have hCB'pos : 0 < CB' := by rw [hCB'def]; positivity
  obtain ⟨Cp, hCppos, hCp⟩ := primitive_LFunction_bound_quarter k hk M hε hδ hδε hCB'pos
  obtain ⟨Cpd, hCpdpos, hCpd⟩ :=
    prod_primeFactors_one_add_rpow_le' (by norm_num : (1/2:ℝ) ≤ 1/2) hδ
  obtain ⟨Cc, hCcpos, hCc⟩ := LFunction_crude_bound
  obtain ⟨Cf, hCfpos, hCf⟩ := crude_absorb_quarter hk hε
  refine ⟨max (Cp * Cpd) (Cc * Cf) + 1, by positivity, ?_⟩
  intro q _inst χ hχ hord σ t hσ hσle
  have hσ12 : (1:ℝ)/2 ≤ σ := by
    have h3k : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) h3k
    linarith
  by_cases hσ1 : σ ≤ 1
  · have hχprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hχprim_ne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ hχ
    have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hord' : orderOf χ.primitiveCharacter ≤ M := by
      rw [orderOf_primitiveCharacter]; exact hord
    have hB' : ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ χ.conductor →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ.primitiveCharacter n‖ ≤
          CB' * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)
            * (H:ℝ)^(1 - 1/((k:ℝ))) := by
      intro N H hN hH hHq
      have hcond1 : (1:ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      have h1 := hCo (q := χ.conductor) (χ := χ.primitiveCharacter) hχprim hχprim_ne hN hH hHq
      have h2 : (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ))) ≤ (M:ℝ)^((3:ℝ)/(2*(k:ℝ))) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hord') (by positivity)
      have h3 : (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)
          ≤ (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) :=
        Real.rpow_le_rpow_of_exponent_le hcond1 (by linarith)
      have hqnn : (0:ℝ) ≤ (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) :=
        Real.rpow_nonneg (by positivity) _
      have hHnn : (0:ℝ) ≤ (H:ℝ)^(1 - 1/((k:ℝ))) := Real.rpow_nonneg (by positivity) _
      have h4 : (Co * (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)
          ≤ (Co * (M:ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) := by
        have h5 : (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)
            ≤ (M:ℝ)^((3:ℝ)/(2*(k:ℝ))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) :=
          mul_le_mul h2 h3 (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
        have h6 := mul_le_mul_of_nonneg_left h5 (le_of_lt hCopos)
        rw [show (Co * (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)
              = Co * ((orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)) by ring,
            show (Co * (M:ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)
              = Co * ((M:ℝ)^((3:ℝ)/(2*(k:ℝ))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)) by ring]
        exact h6
      have h7 : Co * (M:ℝ)^((3:ℝ)/(2*(k:ℝ))) ≤ CB' := by
        rw [hCB'def]; linarith
      have h8 : (Co * (M:ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)
          ≤ CB' * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) :=
        mul_le_mul_of_nonneg_right h7 hqnn
      have h9 : ((Co * (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ)))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4)) * (H:ℝ)^(1 - 1/((k:ℝ)))
          ≤ (CB' * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2)) * (H:ℝ)^(1 - 1/((k:ℝ))) :=
        mul_le_mul_of_nonneg_right (le_trans h4 h8) hHnn
      calc ‖∑ n ∈ Finset.Ioc N (N + H), χ.primitiveCharacter n‖
          ≤ Co * (orderOf χ.primitiveCharacter : ℝ)^((3:ℝ)/(2*(k:ℝ))) * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/4) * (H:ℝ)^(1 - 1/((k:ℝ))) := h1
        _ ≤ CB' * (χ.conductor : ℝ)^((((k:ℝ)+1)/(4*((k:ℝ))^2))+ε/2) * (H:ℝ)^(1 - 1/((k:ℝ))) := h9
    have hpb := hCp χ.conductor χ.primitiveCharacter hχprim hχprim_ne hord' hB' σ t hσ hσ1
    have hred := LFunction_nonprimitive_le χ hχ (σ := σ) hσ12 (t := t)
    have hprod_le : (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ))) ≤ Cpd * (q:ℝ)^δ := by
      refine (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_).trans (hCpd q (NeZero.ne q))
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1/2:ℝ) by linarith)
      linarith
    have hE0 : 0 ≤ ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ := by
      have : (0:ℝ) ≤ (1-σ)*(1+1/(k:ℝ))/4 := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
      linarith [hδε, hε]
    have hqstar : (χ.conductor : ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ)
        ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
      · exact hE0
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)))
            * ‖@DirichletCharacter.LFunction χ.conductor hcond χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ := hred
      _ ≤ (Cpd * (q:ℝ)^δ) * (Cp * (χ.conductor:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1+|t|)) := by
          apply mul_le_mul hprod_le hpb (norm_nonneg _) (by positivity)
      _ = (Cp * Cpd) * ((χ.conductor:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by ring
      _ ≤ (Cp * Cpd) * ((q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by
          have h2 : (0:ℝ) ≤ (q:ℝ)^δ := Real.rpow_nonneg (by positivity) _
          have h3 : (0:ℝ) ≤ (1+|t|) := by positivity
          have h4 := mul_le_mul_of_nonneg_right hqstar h2
          have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ Cp*Cpd*(1+|t|))
          linarith [h5]
      _ = (Cp * Cpd) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          rw [← Real.rpow_add (by exact_mod_cast (NeZero.pos q) : (0:ℝ) < (q:ℝ))]
          rw [show ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε - δ + δ = ((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε by ring]
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cp * Cpd ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_left (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCppos, hCpdpos]
  · have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcb := hCc q χ hχ σ t hσge
    have hca := hCf q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) σ hσge hσle
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ Cc * (1 + Real.log (q:ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (1 + |t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos)
      _ = (Cc * Cf) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by ring
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/4)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cc * Cf ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_right (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCcpos, hCfpos]


end Commons.NumberTheory.DirichletCharacter
