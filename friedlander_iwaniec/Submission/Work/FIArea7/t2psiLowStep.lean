import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.t2psiLowAbel

namespace Work.FIArea7

open Finset

-- Route: for each `t ≤ N / a` the partial sum `∑_{m ≤ t} quadEigen ψ (c * (a*m))` is
-- `LLinear (c*a) t ψ`, so `h32` (Prop. 23.2 at `m = c*a`, `N = t`) bounds it by
-- `C * d * (|k|+1) * τ(c*a)^4 * sqrt(c*a) * (t:ℝ)^{3/4} * log((c*a)*t+2)`, which is at most
-- `C * d * (|k|+1) * τ(c*a)^4 * sqrt(c*a) * ((N:ℝ)/a)^{3/4} * log(c*N+2)` because `t*a ≤ N`;
-- summation by parts with the weight `log` (`Work.FIArea7.abelLogSum`, module
-- `Submission.Work.FIArea7.t2psiLowAbel`) then transfers the bound to the log-weighted sum
-- (`log((N/a:ℕ)+2) ≤ log(c*N+2)` as `c ≥ 1`).
theorem t2psiLowStep (h32 : Work.FIArea7.Prop232) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N c d a : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
        1 ≤ N → 1 ≤ c → 1 ≤ d → 1 ≤ a →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (x y : ℤ), chi (⟨x + 4 * (d : ℤ), y⟩ : GaussianInt) = chi ⟨x, y⟩) →
        (∀ (x y : ℤ), chi (⟨x, y + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨x, y⟩) →
        ‖∑ m ∈ Finset.Icc 1 (N / a),
            ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (a * m))‖
          ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((c * a).divisors.card : ℕ) : ℝ) ^ 4
              * Real.sqrt (c * a) * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
              * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 2 := by
  obtain ⟨C0, hC0pos, h32b⟩ := h32
  refine ⟨8 * C0, by positivity, ?_⟩
  intro N c d a k chi hN hc hd ha hchi hmul hper1 hper2
  -- the single log factor coming from the Abel summation is absorbed into the second `log`
  have hlog_nn : (0:ℝ) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) := by
    apply Real.log_nonneg
    nlinarith [show (1:ℝ) ≤ (c:ℝ) by exact_mod_cast hc, show (1:ℝ) ≤ (N:ℝ) by exact_mod_cast hN]
  -- uniform bound for every partial sum `t ≤ N / a`
  set B : ℝ := C0 * (d:ℝ) * (|(k:ℝ)|+1) * (((c*a).divisors.card : ℕ):ℝ)^4
            * Real.sqrt (((c*a:ℕ):ℝ)) * ((N:ℝ)/(a:ℝ))^((3:ℝ)/4)
            * Real.log ((c:ℝ)*(N:ℝ)+2) with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hca : 1 ≤ c * a := by
    have : 0 < c * a := Nat.mul_pos (by omega) (by omega)
    omega
  have hpartial : ∀ t : ℕ, t ≤ N / a →
      ‖∑ m ∈ Finset.Icc 1 t, quadEigen (grossenChar chi k) (c * (a * m))‖ ≤ B := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [hempty, Finset.sum_empty, norm_zero]
      exact hBnn
    · have ht1 : 1 ≤ t := htpos
      have htle : t * a ≤ N := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp ht
      -- the partial sum is the linear form `L(c*a, t)`
      have hsum_eq : (∑ m ∈ Finset.Icc 1 t, quadEigen (grossenChar chi k) (c * (a * m)))
          = LLinear (c * a) t (grossenChar chi k) := by
        rw [LLinear]
        exact Finset.sum_congr rfl (fun m _ => by congr 1; ring)
      rw [hsum_eq]
      have hb := (h32b t (c*a) d k chi hca hd ht1 hchi hmul hper1 hper2).1
      refine le_trans hb ?_
      rw [hB]
      have ht34 : (t:ℝ)^((3:ℝ)/4) ≤ ((N:ℝ)/(a:ℝ))^((3:ℝ)/4) := by
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        exact le_trans (by exact_mod_cast ht) (Nat.cast_div_le (α := ℝ))
      have hlog : Real.log (((c*a:ℕ):ℝ) * (t:ℝ) + 2) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) := by
        apply Real.log_le_log (by positivity)
        have htleR : (t:ℝ) * (a:ℝ) ≤ (N:ℝ) := by exact_mod_cast htle
        have hcR : (0:ℝ) ≤ (c:ℝ) := by positivity
        have hmm := mul_le_mul_of_nonneg_left htleR hcR
        push_cast
        nlinarith [hmm]
      have hlog1nn : (0:ℝ) ≤ Real.log (((c*a:ℕ):ℝ) * (t:ℝ) + 2) := by
        apply Real.log_nonneg
        have h1 : (1:ℝ) ≤ ((c*a:ℕ):ℝ) := by exact_mod_cast hca
        have h2 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht1
        have h0 : (0:ℝ) ≤ ((c*a:ℕ):ℝ) := by positivity
        have h4 : ((c*a:ℕ):ℝ) * 1 ≤ ((c*a:ℕ):ℝ) * (t:ℝ) := mul_le_mul_of_nonneg_left h2 h0
        rw [mul_one] at h4
        linarith
      have hK : (0:ℝ) ≤ C0 * (d:ℝ) * (|(k:ℝ)|+1) * (((c*a).divisors.card : ℕ):ℝ)^4
          * Real.sqrt (((c*a:ℕ):ℝ)) := by positivity
      have hP34nn : (0:ℝ) ≤ ((N:ℝ)/(a:ℝ))^((3:ℝ)/4) := by positivity
      calc C0*(d:ℝ)*(|(k:ℝ)|+1)*(((c*a).divisors.card : ℕ):ℝ)^4*Real.sqrt (((c*a:ℕ):ℝ))*(t:ℝ)^((3:ℝ)/4)
              * Real.log (((c*a:ℕ):ℝ) * (t:ℝ) + 2)
          ≤ C0*(d:ℝ)*(|(k:ℝ)|+1)*(((c*a).divisors.card : ℕ):ℝ)^4*Real.sqrt (((c*a:ℕ):ℝ))*((N:ℝ)/(a:ℝ))^((3:ℝ)/4)
              * Real.log (((c*a:ℕ):ℝ) * (t:ℝ) + 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht34 hK) hlog1nn
        _ ≤ C0*(d:ℝ)*(|(k:ℝ)|+1)*(((c*a).divisors.card : ℕ):ℝ)^4*Real.sqrt (((c*a:ℕ):ℝ))*((N:ℝ)/(a:ℝ))^((3:ℝ)/4)
              * Real.log ((c:ℝ)*(N:ℝ)+2) :=
            mul_le_mul_of_nonneg_left hlog (mul_nonneg hK hP34nn)
  -- Abel summation with the weight `log`
  have hmain := abelLogSum (fun m => quadEigen (grossenChar chi k) (c*(a*m))) (N/a) B hBnn hpartial
  refine le_trans hmain ?_
  have hlogM : Real.log (((N/a:ℕ):ℝ) + 2) ≤ Real.log ((c:ℝ)*(N:ℝ)+2) := by
    apply Real.log_le_log (by positivity)
    have h1 : ((N/a:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_le_self N a
    nlinarith [h1, show (1:ℝ) ≤ (c:ℝ) by exact_mod_cast hc, show (0:ℝ) ≤ (N:ℝ) by positivity]
  have hstep : 8 * Real.log (((N/a:ℕ):ℝ) + 2) * B ≤ 8 * Real.log ((c:ℝ)*(N:ℝ)+2) * B :=
    mul_le_mul_of_nonneg_right (by linarith) hBnn
  refine le_trans hstep ?_
  have hsq : Real.sqrt ((c:ℝ)*(a:ℝ)) = Real.sqrt (((c*a:ℕ):ℝ)) := by rw [Nat.cast_mul]
  rw [hsq]
  have heq : 8 * Real.log ((c:ℝ)*(N:ℝ)+2) * B
      = 8 * C0 * (d:ℝ) * (|(k:ℝ)|+1) * (((c*a).divisors.card : ℕ):ℝ)^4 * Real.sqrt (((c*a:ℕ):ℝ))
          * ((N:ℝ)/(a:ℝ))^((3:ℝ)/4) * (Real.log ((c:ℝ)*(N:ℝ)+2))^2 := by
    rw [hB]; ring
  rw [heq]

end Work.FIArea7
