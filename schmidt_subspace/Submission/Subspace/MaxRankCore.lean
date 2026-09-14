import Mathlib
import Submission.Subspace.ApproxSpace
import Submission.Subspace.CoeffInv
import Submission.Subspace.ABounds
import Submission.Subspace.GridRefine
import Submission.Subspace.Assembly
import Submission.Subspace.MaxRankParams
import Submission.Subspace.MaxRankNumeric
import Submission.Commons.Algebra.MvPolynomial.card_support_block_le
import Submission.Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_int_le
import Submission.Commons.Analysis.Real.sum_inv_le_two_div
import Submission.Commons.Analysis.Real.log_two_mul_le_mul_of_ge

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.style.haveILetI false

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

theorem max_rank_core {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hL : L.det ≠ 0) (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (gam : Fin (n+1) → ℝ) (hgam1 : ∀ i, gam i ≤ 1) (hsum : ∑ i, gam i < 0)
    (ε S : ℝ) (hεeq : ε = -∑ i, gam i) (hSeqq : S = ∑ i, |gam i|)
    (K : IntermediateField ℚ ℂ) (hKfin : FiniteDimensional ℚ K) (hLK : ∀ i j, L i j ∈ K)
    (MΛ : ℝ) (hMΛ1 : 1 ≤ MΛ) (hMΛ : ∀ i j, ‖lambdaMatC K L hLK i j‖ ≤ MΛ)
    (c : ℕ) (hc : 0 < c) (hint : ∀ i j, IsIntegral ℤ ((c : ↥K) * lambdaMat K L hLK i j))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (C : ℝ) (hC1 : 1 ≤ C)
    (m : ℕ) (hm : 2 ≤ m)
    (R : ℝ) (hR : 2 ≤ R * mrEta n ε S ^ (2 ^ (m - 1)))
    (Q : Fin m → ℝ) (hQ1 : ∀ h, 1 ≤ Q h)
    (hgap : ∀ i j : Fin m, i ≤ j → (Q j) ^ (R ^ ((j : ℕ) - (i : ℕ))) ≤ Q i)
    (b : Fin m → Fin (n+1) → ℤ) (hb0 : ∀ h, b h 0 ≠ 0)
    (hker : ∀ h (x : Fin (n+1) → ℚ),
      x ∈ approxSpace L gam (Q h) ↔ ∑ j, (b h j : ℚ) * x j = 0)
    (hfr : ∀ h, Module.finrank ℚ (approxSpace L gam (Q h)) = n)
    (hcert : ∀ h, θ * Real.log (Q h) ≤
      Height.logHeight₁ (-((b h 1 : ℤ) : ℚ) / ((b h 0 : ℤ) : ℚ)))
    (d : Fin m → ℕ) (hd : ∀ h, 1 ≤ d h)
    (D : ℝ) (hD0 : 0 < D)
    (hDlo : ∀ h, D ≤ (d h : ℝ) * Real.log (Q h))
    (hDhi : ∀ h, (d h : ℝ) * Real.log (Q h) ≤ (1 + mrTheta n ε S) * D)
    (hratio : ∀ i j : Fin m, i ≤ j → (d i : ℝ) ≤
      mrEta n ε S ^ (2 ^ (m-1) * ((j:ℕ)-(i:ℕ))) * (d j : ℝ))
    (F : MvPolynomial (Fin m × Fin (n+1)) ℤ) (hFne : F ≠ 0)
    (hFhom : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin (n+1), u (h,k) = d h)
    (bad : Finset ((Fin m × Fin (n+1)) →₀ ℕ))
    (hbad : ∀ J ∈ bad, MvPolynomial.coeff J
      (MvPolynomial.aeval (PhiB (m := m) (lambdaMatC K L hLK)) (F.map (algebraMap ℤ ℂ))) = 0)
    (hwinF : ∀ J, (∀ h : Fin m, ∑ k : Fin (n+1), J (h,k) = d h) → J ∉ bad →
      ∀ k : Fin (n+1),
        |(∑ h : Fin m, (J (h,k) : ℝ) / (d h : ℝ)) - (m : ℝ) / ((n+1 : ℕ) : ℝ)|
          ≤ (m : ℝ) * mrTheta n ε S)
    (hFcoeff : ∀ u, ‖((F.coeff u : ℤ) : ℂ)‖ ≤ C *
      (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h))
    (hQbig : ∀ h, mrA n ε S θ MΛ C m ≤ Real.log (Q h)) :
    False := by
  classical
  set Θ := mrTheta n ε S with hΘdef
  set η := mrEta n ε S with hηdef
  set BB := mrB n ε S with hBBdef
  set C0 := mrC0 n ε S with hC0def
  set A := mrA n ε S θ MΛ C m with hAdef
  have hε : 0 < ε := by rw [hεeq]; linarith [hsum]
  have hneg : -(∑ i, gam i) ≤ ∑ i, |gam i| := by
    calc -(∑ i, gam i) = ∑ i, -(gam i) := (Finset.sum_neg_distrib _).symm
      _ ≤ ∑ i, |gam i| := Finset.sum_le_sum (fun i _ => neg_le_abs (gam i))
  have hS : 0 < S := by
    rw [hSeqq]
    linarith [hneg, hεeq, hsum]
  have hεS : ε ≤ S := by
    rw [hεeq, hSeqq]
    exact hneg
  have hN2 : 2 ≤ n + 1 := by omega
  have hΘpos : 0 < Θ := mrTheta_pos hε hS
  have hΘhalf : Θ ≤ 1 / 2 := mrTheta_le_half hε hS hεS
  have hΘle1 : Θ ≤ 1 := by linarith
  have hηpos : 0 < η := mrEta_pos hε hS
  have hηhalf : η ≤ 1 / 2 := mrEta_le_half hε hS hεS
  have hηΘ : 4 * η < Θ := mrEta_lt_theta hε hS
  have hB1 : 1 ≤ BB := mrB_one_le
  have hBdiv : ((n : ℝ) + 1) * n / (BB : ℝ) ≤ Θ := mrB_div_le hε hS
  have hC0ge : 1 ≤ C0 := mrC0_one_le
  have hA1 : (1 : ℝ) ≤ A := mrA_ge_one
  have hQbig' : ∀ h : Fin m, A ≤ Real.log (Q h) := hQbig
  have hA9 : 4 * (1 + Θ) * ((n : ℝ) + 1) ≤ A := le_mrA_9
  have hm0 : 0 < m := by omega
  -- `D ≥ A/(1+Θ)` and `D ≥ 4*(n+1)`
  have hDbig : A / (1 + Θ) ≤ D := by
    have h0 := hDhi ⟨0, hm0⟩
    have h1 : (1 : ℝ) ≤ (d ⟨0, hm0⟩ : ℝ) := by exact_mod_cast hd ⟨0, hm0⟩
    have h2 : A ≤ Real.log (Q ⟨0, hm0⟩) := hQbig' _
    have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
    have h3 : (0 : ℝ) < Real.log (Q ⟨0, hm0⟩) := lt_of_lt_of_le hApos h2
    have h4 : A ≤ (d ⟨0, hm0⟩ : ℝ) * Real.log (Q ⟨0, hm0⟩) := by
      calc A ≤ 1 * Real.log (Q ⟨0, hm0⟩) := by rw [one_mul]; exact h2
        _ ≤ (d ⟨0, hm0⟩ : ℝ) * Real.log (Q ⟨0, hm0⟩) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt h3)
    have h5 : A / (1 + Θ) ≤ ((d ⟨0, hm0⟩ : ℝ) * Real.log (Q ⟨0, hm0⟩)) / (1 + Θ) :=
      div_le_div_of_nonneg_right h4 (by positivity)
    have h6 : ((d ⟨0, hm0⟩ : ℝ) * Real.log (Q ⟨0, hm0⟩)) / (1 + Θ) ≤ D := by
      rw [div_le_iff₀ (by positivity)]
      linarith [h0]
    linarith [h5, h6]
  have hD4 : 4 * ((n : ℝ) + 1) ≤ D := by
    have h1 : (1 + Θ) * (4 * ((n : ℝ) + 1)) ≤ A := by linarith [hA9, hΘpos]
    have h2 : 4 * ((n : ℝ) + 1) ≤ A / (1 + Θ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [h1]
    linarith [h2, hDbig]
  -- the per-`h` logarithmic lower bound
  have hA_le_log : ∀ h : Fin m, A ≤ Real.log (Q h) := hQbig'
  have hlogQpos : ∀ h : Fin m, 0 < Real.log (Q h) := fun h =>
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hA1) (hQbig h)
  -- T = ∑ d_h bound
  have hT : (∑ h : Fin m, (d h : ℝ)) ≤ 2 * (1 + Θ) * D / A := by
    have hR2 : 2 ≤ R := by
      have hηpow1 : mrEta n ε S ^ (2 ^ (m - 1)) ≤ 1 :=
        pow_le_one₀ (le_of_lt hηpos) (le_trans hηhalf (by norm_num))
      have hηpow0 : 0 < mrEta n ε S ^ (2 ^ (m - 1)) := pow_pos hηpos _
      nlinarith [hR, hηpow1, hηpow0]
    have hdec : ∀ i j : Fin m, i ≤ j → R ^ ((j:ℕ)-(i:ℕ)) * Real.log (Q j) ≤ Real.log (Q i) := by
      intro i j hij
      have h1 : (Q j) ^ (R ^ ((j:ℕ)-(i:ℕ))) ≤ Q i := hgap i j hij
      have hQj : (0:ℝ) < Q j := lt_of_lt_of_le zero_lt_one (hQ1 j)
      have h2 := Real.log_le_log (Real.rpow_pos_of_pos hQj _) h1
      rw [Real.log_rpow hQj] at h2
      exact h2
    have hsum_inv : ∑ h : Fin m, 1 / Real.log (Q h) ≤ 2 / A :=
      Commons.Analysis.Real.sum_inv_le_two_div A R (fun h => Real.log (Q h)) (lt_of_lt_of_le zero_lt_one hA1) hR2
        hA_le_log (fun i j hij => by
          have := hdec i j hij
          simpa using this)
    have hle : ∀ h : Fin m, (d h : ℝ) ≤ (1 + Θ) * D / Real.log (Q h) := by
      intro h
      have h0 := hDhi h
      rw [le_div_iff₀ (hlogQpos h)]
      linarith [h0]
    calc (∑ h : Fin m, (d h : ℝ)) ≤ ∑ h : Fin m, (1 + Θ) * D / Real.log (Q h) :=
          Finset.sum_le_sum (fun h _ => hle h)
      _ = ((1 + Θ) * D) * ∑ h : Fin m, 1 / Real.log (Q h) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun h _ => by ring
      _ ≤ ((1 + Θ) * D) * (2 / A) := by
          refine mul_le_mul_of_nonneg_left hsum_inv (by positivity)
      _ = 2 * (1 + Θ) * D / A := by ring
  have hdn : ∀ h : Fin m, ((d h : ℝ) + n) ≤ 2 * D := by
    intro h
    have h0 := hDhi h
    have h1 : (d h : ℝ) ≤ (1 + Θ) * D := by
      have hlog := hlogQpos h
      calc (d h : ℝ) = (d h : ℝ) * 1 := (mul_one _).symm
        _ ≤ (d h : ℝ) * Real.log (Q h) :=
            mul_le_mul_of_nonneg_left (by linarith [hA_le_log h, hA1]) (by positivity)
        _ ≤ (1 + Θ) * D := h0
    have hnD : (n : ℝ) ≤ D := by
      have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have h2 : ((n : ℝ) + 1) ≤ 4 * ((n : ℝ) + 1) := by
        have h3 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        linarith
      calc (n : ℝ) ≤ (n : ℝ) + 1 := h1
        _ ≤ 4 * ((n : ℝ) + 1) := h2
        _ ≤ D := hD4
    have h4 : (n : ℝ) ≤ (1 - Θ) * D := by
      have h5 : (1 / 2) * D ≤ (1 - Θ) * D := by nlinarith [hΘhalf, hD0]
      have h6 : (n : ℝ) ≤ (1 / 2) * D := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [hD4]
      linarith
    linarith [h1, h4]
  -- ============ the logarithm of the Siegel coefficient bound ============
  have hP1pos : (0 : ℝ) < ∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ) :=
    Finset.prod_pos fun h _ => by
      have := Nat.choose_pos (show n ≤ d h + n by omega); exact_mod_cast this
  have hBge1 : (1 : ℝ) ≤ C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
      * (C * MΛ) ^ (∑ h : Fin m, d h) := by
    have h1 : (1 : ℝ) ≤ C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) :=
      one_le_mul_of_one_le_of_one_le hC1 (Finset.one_le_prod (fun h _ => by
        have := Nat.choose_pos (show n ≤ d h + n by omega); exact_mod_cast this))
    have h2 : (1 : ℝ) ≤ (C * MΛ) ^ (∑ h : Fin m, d h) :=
      one_le_pow₀ (one_le_mul_of_one_le_of_one_le hC1 hMΛ1)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hBnd0 : (0 : ℝ) < C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
      * (C * MΛ) ^ (∑ h : Fin m, d h) := lt_of_lt_of_le zero_lt_one hBge1
  have hlogExpand : Real.log (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
        * (C * MΛ) ^ (∑ h : Fin m, d h))
      ≤ Real.log C + (n : ℝ) * (m : ℝ) * Real.log (2 * D)
        + (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ) := by
    have hlogexp : Real.log (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
        * (C * MΛ) ^ (∑ h : Fin m, d h))
        = Real.log C + Real.log (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
          + ((∑ h : Fin m, d h : ℕ) : ℝ) * Real.log (C * MΛ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < C)) (ne_of_gt hP1pos), Real.log_pow]
    rw [hlogexp]
    have hprod : Real.log (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
        ≤ ((n : ℝ) * (m : ℝ)) * Real.log (2 * D) := by
      have hchoose : ∀ h : Fin m, (((d h + n).choose n : ℕ) : ℝ) ≤ (2 * D) ^ n := by
        intro h
        have h1 : (((d h + n).choose n : ℕ) : ℝ) ≤ ((d h + n : ℕ) : ℝ) ^ n := by
          exact_mod_cast Nat.choose_le_pow (d h + n) n
        have hbase : ((d h + n : ℕ) : ℝ) ≤ 2 * D := by
          have := hdn h; push_cast at this ⊢; linarith
        exact le_trans h1 (pow_le_pow_left₀ (by positivity) hbase n)
      have h1 : (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) ≤ (2 * D) ^ (n * m) := by
        calc (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) ≤ ∏ h : Fin m, (2 * D) ^ n :=
              Finset.prod_le_prod (fun h _ => by positivity) (fun h _ => hchoose h)
          _ = (2 * D) ^ (n * m) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      have := Real.log_le_log hP1pos h1
      rw [Real.log_pow] at this
      calc Real.log (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
          ≤ ((n * m : ℕ) : ℝ) * Real.log (2 * D) := this
        _ = ((n : ℝ) * (m : ℝ)) * Real.log (2 * D) := by push_cast; ring
    have hcast : (((∑ h : Fin m, d h : ℕ)) : ℝ) = ∑ h : Fin m, (d h : ℝ) := by
      push_cast; rfl
    rw [hcast]
    linarith [hprod]
  -- ============ the Siegel coefficient bound on `hZ F` ============
  have hSiegel : hZ F ≤ Real.log C + (n : ℝ) * (m : ℝ) * Real.log (2 * D)
      + (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ) := by
    have hcoeff : ∀ u : (Fin m × Fin (n+1)) →₀ ℕ,
        ((((F.coeff u).natAbs : ℕ)) : ℝ)
          ≤ C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h) := by
      intro u
      have h := hFcoeff u
      have h2 : ‖((F.coeff u : ℤ) : ℂ)‖ = (((F.coeff u).natAbs : ℕ) : ℝ) := by
        rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
      rwa [h2] at h
    have hlog := Commons.NumberTheory.Height.MvPolynomial.logHeight_gP_int_le F
      (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h))
      hBge1 hcoeff
    have hZdef : hZ F = Height.logHeight
        (Commons.NumberTheory.Height.MvPolynomial.gP (F.map (Int.castRingHom ℚ))) := rfl
    rw [hZdef]
    exact le_trans hlog hlogExpand
  -- ============ the height condition of the non-vanishing lemma ============
  have hcond : η ^ (2 ^ (m - 1)) *
      (⨅ h : Fin m, (d h : ℝ) *
        Height.logHeight₁ (-((b h 1 : ℤ) : ℚ) / ((b h 0 : ℤ) : ℚ)))
      ≥ hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ)) := by
    have hinf : (⨅ h : Fin m, (d h : ℝ) *
        Height.logHeight₁ (-((b h 1 : ℤ) : ℚ) / ((b h 0 : ℤ) : ℚ))) ≥ θ * D := by
      haveI : Nonempty (Fin m) := ⟨⟨0, hm0⟩⟩
      refine le_ciInf ?_
      intro h
      have h1 := hcert h
      have h2 := hDlo h
      have h3 : (1 : ℝ) ≤ (d h : ℝ) := by exact_mod_cast hd h
      nlinarith [h1, h2, h3, hθ0]
    have hlogC := mrnum_logC (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D)
      (m := m) hε hS hθ0 hC1 hDbig
    have hlogD := mrnum_logD (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D)
      (m := m) hε hS hθ0 (by omega) (by omega) hD0 hDbig
    have hT'' := mrnum_T (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D)
      (T := ∑ h : Fin m, (d h : ℝ)) (m := m) hε hS hθ0 hC1 hMΛ1 hD0 hDbig
      (lt_of_lt_of_le zero_lt_one hA1) hT
    have h1 : hZ F ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8
        + (n : ℝ) * (m : ℝ) * Real.log (2 * D) + (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ) := by
      linarith [hSiegel, hlogC]
    have h2 : hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))
        ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D := by
      have h5 : (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ)
          + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))
          = (∑ h : Fin m, (d h : ℝ)) * (Real.log (C * MΛ) + 100 * (m : ℝ)) := by ring
      have hT3 : (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ)
          + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))
          ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 2 := by
        rw [h5]; exact hT''
      calc hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))
          ≤ (mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8 + (n : ℝ) * (m : ℝ) * Real.log (2 * D)
              + (∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ))
            + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ)) := add_le_add h1 le_rfl
        _ = (mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8 + (n : ℝ) * (m : ℝ) * Real.log (2 * D))
              + ((∑ h : Fin m, (d h : ℝ)) * Real.log (C * MΛ)
                + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))) := by ring
        _ ≤ (mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8 + mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 8)
              + mrEta n ε S ^ (2 ^ (m - 1)) * θ * D / 2 :=
            add_le_add (add_le_add le_rfl hlogD) hT3
        _ = 3 / 4 * (mrEta n ε S ^ (2 ^ (m - 1)) * θ * D) := by ring
        _ ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D := by
            have hx : (0:ℝ) ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D := by positivity
            linarith
    calc hZ F + 100 * (m : ℝ) * (∑ h : Fin m, (d h : ℝ))
        ≤ mrEta n ε S ^ (2 ^ (m - 1)) * θ * D := h2
      _ = η ^ (2 ^ (m - 1)) * (θ * D) := by rw [hηdef]; ring
      _ ≤ η ^ (2 ^ (m - 1)) *
          (⨅ h : Fin m, (d h : ℝ) *
            Height.logHeight₁ (-((b h 1 : ℤ) : ℚ) / ((b h 0 : ℤ) : ℚ))) :=
          mul_le_mul_of_nonneg_left hinf (pow_nonneg (le_of_lt hηpos) _)
  -- ============ the grid generators ============
  have hgen : ∀ h : Fin m, ∃ g : Fin n → (Fin (n+1) → ℤ),
      (∀ l, g l ∈ approxBox L gam (Q h)) ∧ LinearIndependent ℚ (fun l => intCastVec (g l)) := by
    intro h
    exact exists_fin_box_independent (σ := Fin (n+1)) n (approxBox L gam (Q h))
      (approxSpace L gam (Q h)) Submodule.subset_span rfl (hfr h)
  choose g hgbox hgli using hgen
  have hgker : ∀ h l, ∑ j, ((b h j : ℤ) : ℚ) * ((g h l j : ℤ) : ℚ) = 0 := by
    intro h l
    have hmem : intCastVec (g h l) ∈ approxSpace L gam (Q h) :=
      mem_approxSpace_of_mem_box (hgbox h l)
    have := (hker h (intCastVec (g h l))).mp hmem
    simpa [intCastVec] using this
  have hspan' : ∀ h (y : Fin (n+1) → ℚ),
      (∑ j, ((b h j : ℤ) : ℚ) * y j = 0) →
      y ∈ Submodule.span ℚ (Set.range (fun l : Fin n => fun j => ((g h l j : ℤ) : ℚ))) := by
    intro h y hy
    have hle : Submodule.span ℚ (Set.range (fun l : Fin n => intCastVec (g h l)))
        ≤ approxSpace L gam (Q h) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_approxSpace_of_mem_box (hgbox h l)
    have hfr1 : Module.finrank ℚ
        ↥(Submodule.span ℚ (Set.range (fun l : Fin n => intCastVec (g h l)))) = n := by
      rw [finrank_span_eq_card (hgli h), Fintype.card_fin]
    have heq : Submodule.span ℚ (Set.range (fun l : Fin n => intCastVec (g h l)))
        = approxSpace L gam (Q h) :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr1, hfr h])
    rw [heq]
    exact (hker h y).mpr hy
  -- ============ the non-vanishing lemma ============
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm0⟩
  haveI : NeZero (n+1) := ⟨by omega⟩
  obtain ⟨z, J, hz, hJ, hJne⟩ :=
    nonvanish_grid (m := m) (N := n+1) (by omega) F hFne d
      (isBlockHom_map_intCast_rat hFhom) d hd (fun _ => le_refl _)
      (fun h j => ((b h j : ℤ) : ℚ)) (fun h => by exact_mod_cast hb0 h)
      (1 : Fin (n+1)) (by show (1 % (n+1) : ℕ) = 1; exact Nat.mod_eq_of_lt (by omega)) g hgker hspan'
      (mrTheta n ε S) (mrEta n ε S) hΘpos hηpos hηhalf hηΘ hratio hcond BB hB1
  -- ============ the grid point and the coefficient vector ============
  set xx : Fin m × Fin (n+1) → ℤ :=
    fun hi => ∑ l, z (hi.1, l) * g hi.1 l hi.2 with hxxdef
  set u : Fin m × Fin (n+1) → ℂ :=
    fun q => ∑ i, L q.2 i * ((xx (q.1, i) : ℤ) : ℂ) with hudef
  have hxu : ∀ q : Fin m × Fin (n+1), algebraMap ℤ ℂ (xx q)
      = ∑ k : Fin (n+1), lambdaMatC K L hLK k q.2 * u (q.1, k) := by
    intro q
    obtain ⟨h, j⟩ := q
    have h1 := congrFun (lambdaMatC_mulVec_eq K L hLK hL (fun i => xx (h, i))) j
    simpa [hudef] using h1
  have hne : MvPolynomial.aeval (fun q : Fin m × Fin (n+1) => algebraMap ℤ ℂ (xx q))
      (pderivIterDiv J (F.map (algebraMap ℤ ℂ))) ≠ 0 :=
    (aeval_pderivIterDiv_intCast_ne_zero_iff F J xx).mpr hJne
  have hu : ∀ q : Fin m × Fin (n+1), ‖u q‖ ≤ C0 * Q q.1 ^ (gam q.2) := by
    intro q
    obtain ⟨h, k⟩ := q
    have hzB : ∀ l, ‖((z (h,l) : ℤ) : ℂ)‖ ≤ (BB : ℝ) := by
      intro l
      have h1 := hz (h, l)
      have h2 : ‖((z (h,l) : ℤ) : ℂ)‖ = ((|z (h,l)| : ℤ) : ℝ) := by
        rw [Complex.norm_intCast, ← Int.cast_abs]
      rw [h2]
      exact_mod_cast h1
    have hbox : ∀ l, ‖(∑ i, L k i * ((g h l i : ℤ) : ℂ))‖ ≤ (Q h) ^ (gam k) := by
      intro l
      exact (mem_approxBox_iff.mp (hgbox h l)) k
    have hule : u (h, k) = ∑ l, (z (h,l) : ℂ) * (∑ i, L k i * ((g h l i : ℤ) : ℂ)) := by
      simp only [hudef, hxxdef, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun i _ => by ring
    calc ‖u (h,k)‖ = ‖∑ l, (z (h,l) : ℂ) * (∑ i, L k i * ((g h l i : ℤ) : ℂ))‖ := by rw [hule]
      _ ≤ ∑ l, ‖(z (h,l) : ℂ) * (∑ i, L k i * ((g h l i : ℤ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ l, (BB : ℝ) * ((Q h) ^ (gam k)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [norm_mul]
          exact mul_le_mul (hzB l) (hbox l) (norm_nonneg _) (by positivity)
      _ = (n : ℝ) * (BB : ℝ) * ((Q h) ^ (gam k)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          push_cast; ring
      _ ≤ C0 * Q h ^ (gam k) := by
          have hC0' : (n : ℝ) * (BB : ℝ) ≤ C0 := by
            rw [hC0def, hBBdef, mrC0]; linarith
          have hp : 0 ≤ (Q h) ^ (gam k) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (hQ1 h))) _
          exact mul_le_mul_of_nonneg_right hC0' hp
  have hsmall : ((m : ℝ) * mrTheta n ε S
      + Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin (n+1) => d hi.1) J
      + mrTheta n ε S * (m : ℝ)) * (∑ k : Fin (n+1), |gam k|)
      < ε * (m : ℝ) / (2 * (((n+1 : ℕ)) : ℝ)) := by
    have hbase := mr_hsmall (n := n) hε hS hεS gam (by rw [hSeqq]) (m := m) (by omega)
    have hsum0 : (0 : ℝ) ≤ ∑ k : Fin (n+1), |gam k| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    have hJ' : Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin (n+1) => d hi.1) J
        ≤ (m : ℝ) * mrTheta n ε S + (m : ℝ) * ((n : ℝ) + 1) * n / (BB : ℝ) := by
      have := hJ
      simpa using this
    have hle : (m : ℝ) * mrTheta n ε S
        + Commons.Algebra.MvPolynomial.indexWt (fun hi : Fin m × Fin (n+1) => d hi.1) J
        + mrTheta n ε S * (m : ℝ)
        ≤ (m : ℝ) * mrTheta n ε S
          + ((m : ℝ) * mrTheta n ε S + (m : ℝ) * ((n : ℝ) + 1) * n / (BB : ℝ))
          + mrTheta n ε S * (m : ℝ) := by linarith [hJ']
    have hbase' : ((m : ℝ) * mrTheta n ε S
        + ((m : ℝ) * mrTheta n ε S + (m : ℝ) * ((n : ℝ) + 1) * n / (BB : ℝ))
        + mrTheta n ε S * (m : ℝ)) * (∑ k : Fin (n+1), |gam k|)
        < ε * (m : ℝ) / (2 * (((n+1 : ℕ)) : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact hbase
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hsum0) hbase'
  have hLc : Real.log (F.support.card : ℝ)
      ≤ ((n : ℝ) + 1) * (m : ℝ) * Real.log (2 * D) := by
    have hcardF : F.support.card ≤ ∏ h : Fin m, (d h + 1) ^ (n+1) := by
      have h1 : (F.map (Int.castRingHom ℂ)).support.card
          ≤ ∏ h : Fin m, (d h + 1) ^ (n+1) := by
        refine Commons.Algebra.MvPolynomial.card_support_block_le
          (F.map (Int.castRingHom ℂ)) d ?_
        intro J hJ h
        rw [MvPolynomial.support_map_of_injective _ Int.cast_injective] at hJ
        exact le_of_eq (hFhom J hJ h)
      rwa [MvPolynomial.support_map_of_injective _ Int.cast_injective] at h1
    have hcard0 : (0 : ℝ) < (F.support.card : ℝ) := by
      have : 0 < F.support.card := Finset.card_pos.mpr (MvPolynomial.support_nonempty.mpr hFne)
      exact_mod_cast this
    have hbase : ∀ h : Fin m, (d h : ℝ) + 1 ≤ 2 * D := by
      intro h
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have := hdn h
      linarith
    have h2 : Real.log (F.support.card : ℝ)
        ≤ Real.log ((∏ h : Fin m, (d h + 1) ^ (n+1) : ℕ) : ℝ) := by
      refine Real.log_le_log hcard0 ?_
      exact_mod_cast hcardF
    have h3 : Real.log ((∏ h : Fin m, (d h + 1) ^ (n+1) : ℕ) : ℝ)
        = ((n : ℝ) + 1) * (∑ h : Fin m, Real.log ((d h : ℝ) + 1)) := by
      rw [Nat.cast_prod, Real.log_prod]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun h _ => by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      · intro h _; positivity
    have h4 : ∑ h : Fin m, Real.log ((d h : ℝ) + 1) ≤ (m : ℝ) * Real.log (2 * D) := by
      calc ∑ h : Fin m, Real.log ((d h : ℝ) + 1) ≤ ∑ h : Fin m, Real.log (2 * D) :=
            Finset.sum_le_sum fun h _ => Real.log_le_log (by positivity) (hbase h)
        _ = (m : ℝ) * Real.log (2 * D) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    calc Real.log (F.support.card : ℝ)
        ≤ Real.log ((∏ h : Fin m, (d h + 1) ^ (n+1) : ℕ) : ℝ) := h2
      _ = ((n : ℝ) + 1) * (∑ h : Fin m, Real.log ((d h : ℝ) + 1)) := h3
      _ ≤ ((n : ℝ) + 1) * ((m : ℝ) * Real.log (2 * D)) := mul_le_mul_of_nonneg_left h4 hN0
      _ = ((n : ℝ) + 1) * (m : ℝ) * Real.log (2 * D) := by ring
  have hLp : Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ (n+1))
      ≤ ((n : ℝ) + 1) * (m : ℝ) * Real.log (2 * D) := by
    have hbase : ∀ h : Fin m, (d h : ℝ) + 1 ≤ 2 * D := by
      intro h
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have := hdn h
      linarith
    have h3 : Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ (n+1))
        = ((n : ℝ) + 1) * (∑ h : Fin m, Real.log ((d h : ℝ) + 1)) := by
      rw [Real.log_prod]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun h _ => by rw [Real.log_pow]; push_cast; ring
      · intro h _; positivity
    have h4 : ∑ h : Fin m, Real.log ((d h : ℝ) + 1) ≤ (m : ℝ) * Real.log (2 * D) := by
      calc ∑ h : Fin m, Real.log ((d h : ℝ) + 1) ≤ ∑ h : Fin m, Real.log (2 * D) :=
            Finset.sum_le_sum fun h _ => Real.log_le_log (by positivity) (hbase h)
        _ = (m : ℝ) * Real.log (2 * D) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h3]
    have hN0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    calc ((n : ℝ) + 1) * (∑ h : Fin m, Real.log ((d h : ℝ) + 1))
        ≤ ((n : ℝ) + 1) * ((m : ℝ) * Real.log (2 * D)) := mul_le_mul_of_nonneg_left h4 hN0
      _ = ((n : ℝ) + 1) * (m : ℝ) * Real.log (2 * D) := by ring
  have hbig : 2 * (((n+1 : ℕ)) : ℝ) * (Real.log (F.support.card : ℝ)
      + Real.log (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h))
      + (((∑ h : Fin m, d h : ℕ)) : ℝ) * ((((n+1 : ℕ)) : ℝ) * Real.log 2)
      + Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ (n+1))
      + (((∑ h : Fin m, d h : ℕ)) : ℝ) * Real.log ((((n+1 : ℕ)) : ℝ) * MΛ + 1)
      + (((∑ h : Fin m, d h : ℕ)) : ℝ) * Real.log C0) < D * ε * (m : ℝ) := by
    have hT4 : (((∑ h : Fin m, d h : ℕ)) : ℝ)
        ≤ 2 * (1 + mrTheta n ε S) * D / mrA n ε S θ MΛ C m := by
      push_cast
      exact hT
    have hLb' : Real.log (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ))
          * (C * MΛ) ^ (∑ h : Fin m, d h))
        ≤ Real.log C + (n : ℝ) * (m : ℝ) * Real.log (2 * D)
          + (((∑ h : Fin m, d h : ℕ)) : ℝ) * Real.log (C * MΛ) := by
      push_cast
      exact hlogExpand
    simpa [Nat.cast_add, Nat.cast_one, hC0def, mrC0] using
      mrnum_hbig (n := n) (ε := ε) (S := S) (θ := θ) (MΛ := MΛ) (C := C) (D := D)
        (Lc := Real.log (F.support.card : ℝ))
        (Lb := Real.log (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h)))
        (Lp := Real.log (∏ h : Fin m, ((d h : ℝ) + 1) ^ (n+1)))
        (T := (((∑ h : Fin m, d h : ℕ)) : ℝ)) (m := m)
        (by omega) (by omega) hε hS hεS hθ0 hC1 hMΛ1 hD0 hA1 hDbig hLc hLb' hLp hT4
        (by positivity)
  have hΛi : Matrix.transpose (Matrix.of L) * lambdaMatC K L hLK = 1 := by
    have h := lambdaMatC_transpose_mul K L hLK hL
    have h2 := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using h2
  exact A_bounds (m := m) (N := n+1) hm0 (by omega) d hd F hFne hFhom
    (lambdaMatC K L hLK) (Matrix.transpose (Matrix.of L)) hΛi
    MΛ (by linarith) hMΛ
    (C * (∏ h : Fin m, (((d h + n).choose n : ℕ) : ℝ)) * (C * MΛ) ^ (∑ h : Fin m, d h))
    hBnd0 hFcoeff bad hbad (mrTheta n ε S) (le_of_lt hΘpos) hwinF
    xx u hxu gam ε hε (by rw [hεeq]; linarith) Q (fun h => lt_of_lt_of_le zero_lt_one (hQ1 h))
    D (mrTheta n ε S) C0 hD0 (le_of_lt hΘpos) hC0ge hDlo hDhi hu J hne hsmall hbig

end Submission.Subspace
