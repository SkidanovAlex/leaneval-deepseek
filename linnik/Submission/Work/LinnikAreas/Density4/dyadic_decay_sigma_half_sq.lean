import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Work.LinnikAreas.Density4.sigma_half_sq_divisor_bound
import Submission.Work.LinnikAreas.Density4.core_dyadic_sum_bound
import Submission.Work.LinnikAreas.Density4.tau_rpow_sum_bound

namespace Work.LinnikAreas.Density4

open Finset

/-!
# The squared `σ_{-1/2}`-weighted dyadic decay of Linnik's bookkeeping

We prove `Work.LinnikAreas.Density4.dyadic_decay_sigma_half_sq`: the sum

`Σ_{δ ≤ V} μ²(δ) φ(δ)/δ² · (Σ_{d ∣ δ} d^{-1/2})² · (log (2 + V/δ))^{-2A}`

is bounded by an absolute constant, uniformly in `V` and for every `A ≥ 1`.

The proof has three inputs:

* `sigma_half_sq_divisor_bound`: `μ²(n) φ(n) (Σ_{d∣n} d^{-1/2})² ≤ n Σ_{e∣n} τ(e) e^{-1/2}`;
* `core_dyadic_sum_bound`: `Σ_{m ≤ N} (1/m) (log (2 + N/m))^{-2} = O(1)` uniformly in `N`;
* `tau_rpow_sum_bound`: `Σ_{e ≤ N} τ(e) e^{-3/2} ≤ 16`.

The Euler factor `φ(δ)/δ` is what makes the squarefree local factor `(1-1/p)(1+p^{-1/2})²`
dominated by `1 + 2p^{-1/2}`, i.e. by the `τ`-weight; the log-power saving with `A ≥ 1`
then beats the harmonic divergence `Σ 1/δ`, while the surviving `Σ τ(e)e^{-3/2} = ζ(3/2)²`
converges.
-/

private lemma one_le_log_two_add (V δ : ℕ) (hδ1 : 1 ≤ δ) (hδV : δ ≤ V) :
    (1:ℝ) ≤ Real.log (2 + (V:ℝ)/(δ:ℝ)) := by
  have hδpos : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ1
  have hVδ : (1:ℝ) ≤ (V:ℝ)/(δ:ℝ) := by
    rw [one_le_div hδpos]; exact_mod_cast hδV
  have h3 : (3:ℝ) ≤ 2 + (V:ℝ)/(δ:ℝ) := by linarith
  have hlog3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_three
  linarith [Real.log_le_log (by norm_num : (0:ℝ) < 3) h3]

private lemma rpow_neg_two_mul_le (x A : ℝ) (hx : 1 ≤ x) (hA : 1 ≤ A) :
    x ^ (-2 * A) ≤ x ^ (-2 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hx (by linarith)

private lemma card_div_sqrt_mul_inv (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ)/Real.sqrt (n:ℝ) * (1/(n:ℝ)) = (n.divisors.card : ℝ)/((n:ℝ)^(3/2:ℝ)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hpow : (n:ℝ)^(3/2:ℝ) = (n:ℝ) * Real.sqrt (n:ℝ) := by
    rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hnpos, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow]
  field_simp

private theorem coreSum_le_of_le (K : ℝ)
    (hK : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, (1:ℝ)/(m:ℝ) *
        (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)) ≤ K)
    (N : ℕ) (M : ℝ) (hM : (N:ℝ) ≤ M) :
    (∑ m ∈ Finset.Icc 1 N, (1:ℝ)/(m:ℝ) *
        (Real.log (2 + M/(m:ℝ)))^(-2:ℝ)) ≤ K := by
  refine le_trans (Finset.sum_le_sum ?_) (hK N)
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hNN : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hNm : (0:ℝ) ≤ (N:ℝ)/(m:ℝ) := div_nonneg hNN hmpos.le
  have hlog_pos : 0 < Real.log (2 + (N:ℝ)/(m:ℝ)) := by
    exact Real.log_pos (by linarith)
  have hle : Real.log (2 + (N:ℝ)/(m:ℝ)) ≤ Real.log (2 + M/(m:ℝ)) := by
    refine Real.log_le_log (by linarith) ?_
    have := div_le_div_of_nonneg_right hM hmpos.le
    linarith
  have hkey := Real.rpow_le_rpow_of_nonpos hlog_pos hle (by norm_num : (-2:ℝ) ≤ 0)
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

theorem dyadic_decay_sigma_half_sq_of (K : ℝ)
    (h1 : ∀ n : ℕ, ((ArithmeticFunction.moebius n : ℝ)^2) * (n.totient : ℝ) *
          (∑ d ∈ n.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2
        ≤ (n:ℝ) * ∑ e ∈ n.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ))
    (h2 : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, (1:ℝ)/(m:ℝ) *
          (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)) ≤ K)
    (h3 : ∀ N : ℕ, (∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ)/(e:ℝ)^(3/2:ℝ)) ≤ 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : ℕ) (A : ℝ), 1 ≤ A →
      (∑ δ ∈ Finset.Icc 1 V, ((ArithmeticFunction.moebius δ : ℝ)^2) * (Nat.totient δ : ℝ) / ((δ:ℝ)^2) *
        (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2 *
        (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2*A)) ≤ C := by
  have hK'0 : (0:ℝ) ≤ max K 0 := le_max_right _ _
  refine ⟨max 1 (16 * max K 0), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro V A hA
  have stepA :
      (∑ δ ∈ Finset.Icc 1 V, ((ArithmeticFunction.moebius δ : ℝ)^2) * (Nat.totient δ : ℝ) / ((δ:ℝ)^2) *
        (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2 *
        (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2*A))
      ≤ ∑ δ ∈ Finset.Icc 1 V, ∑ e ∈ δ.divisors,
          (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(δ:ℝ)) * (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2:ℝ) := by
    apply Finset.sum_le_sum
    intro δ hδ
    obtain ⟨hδ1, hδV⟩ := Finset.mem_Icc.mp hδ
    have hδpos : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ1
    have hδpos2 : (0:ℝ) < (δ:ℝ)^2 := by positivity
    have hB : 0 ≤ ∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) := by
      apply Finset.sum_nonneg
      intro e he
      exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hsum_eq : ∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(δ:ℝ)) *
          (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2:ℝ)
        = (∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ)) *
          (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2:ℝ) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [hsum_eq]
    have hdiv : ((ArithmeticFunction.moebius δ : ℝ)^2) * (δ.totient : ℝ) / ((δ:ℝ)^2) *
          (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2
        ≤ (∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ)) := by
      have hb := h1 δ
      have hstep := div_le_div_of_nonneg_right hb hδpos2.le
      calc ((ArithmeticFunction.moebius δ : ℝ)^2) * (δ.totient : ℝ) / ((δ:ℝ)^2) *
              (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2
          = (((ArithmeticFunction.moebius δ : ℝ)^2) * (δ.totient : ℝ) *
              (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2) / ((δ:ℝ)^2) := by ring
        _ ≤ ((δ:ℝ) * ∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) / ((δ:ℝ)^2) := hstep
        _ = (∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ)) := by
              rw [pow_two, mul_div_mul_left _ _ hδpos.ne', div_eq_mul_inv, one_div]
    have hL : (1:ℝ) ≤ Real.log (2 + (V:ℝ)/(δ:ℝ)) := one_le_log_two_add V δ hδ1 hδV
    have hw := rpow_neg_two_mul_le _ A hL hA
    have hwnn : (0:ℝ) ≤ (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2*A) :=
      Real.rpow_nonneg (by linarith) _
    have hQnn : (0:ℝ) ≤ (∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ)) :=
      mul_nonneg hB (by positivity)
    calc ((ArithmeticFunction.moebius δ : ℝ)^2) * (δ.totient : ℝ) / ((δ:ℝ)^2) *
            (∑ d ∈ δ.divisors, (1:ℝ)/Real.sqrt (d:ℝ))^2 *
            (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2*A)
        ≤ ((∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ))) *
            (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2*A) :=
          mul_le_mul_of_nonneg_right hdiv hwnn
      _ ≤ ((∑ e ∈ δ.divisors, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ)) * (1/(δ:ℝ))) *
            (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2:ℝ) :=
          mul_le_mul_of_nonneg_left hw hQnn
  have stepB : (∑ δ ∈ Finset.Icc 1 V, ∑ e ∈ δ.divisors,
          (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(δ:ℝ)) * (Real.log (2 + (V:ℝ)/(δ:ℝ)))^(-2:ℝ))
      = ∑ e ∈ Finset.Icc 1 V, ∑ m ∈ Finset.Icc 1 (V/e),
          (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/((e*m):ℝ)) *
            (Real.log (2 + (V:ℝ)/((e*m):ℝ)))^(-2:ℝ) := by
    have h := sum_Icc_div_reindex (M := ℝ) V (fun _ => True)
      (fun d m => (d.divisors.card : ℝ)/Real.sqrt (d:ℝ) * (1/((d*m):ℝ)) *
            (Real.log (2 + (V:ℝ)/((d*m):ℝ)))^(-2:ℝ))
    simp only [Finset.filter_true] at h
    rw [h]
    refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun d hd => ?_))
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  refine le_trans (le_trans stepA (le_of_eq stepB)) ?_
  have key : (∑ e ∈ Finset.Icc 1 V, ∑ m ∈ Finset.Icc 1 (V/e),
          (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/((e*m):ℝ)) *
            (Real.log (2 + (V:ℝ)/((e*m):ℝ)))^(-2:ℝ)) ≤ (max K 0) * 16 := by
    calc (∑ e ∈ Finset.Icc 1 V, ∑ m ∈ Finset.Icc 1 (V/e),
            (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/((e*m):ℝ)) *
              (Real.log (2 + (V:ℝ)/((e*m):ℝ)))^(-2:ℝ))
        ≤ ∑ e ∈ Finset.Icc 1 V, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) * (max K 0) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨he1, heV⟩ := Finset.mem_Icc.mp he
          have hepos : (0:ℝ) < (e:ℝ) := by exact_mod_cast he1
          have hMe : ((V/e : ℕ) : ℝ) ≤ (V:ℝ)/(e:ℝ) := Nat.cast_div_le
          have hinner : (∑ m ∈ Finset.Icc 1 (V/e),
                (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/((e*m):ℝ)) *
                  (Real.log (2 + (V:ℝ)/((e*m):ℝ)))^(-2:ℝ))
              = (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) *
                (∑ m ∈ Finset.Icc 1 (V/e), (1/(m:ℝ)) *
                  (Real.log (2 + ((V:ℝ)/(e:ℝ))/(m:ℝ)))^(-2:ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            have h1 : (1:ℝ)/((e:ℝ)*(m:ℝ)) = (1/(e:ℝ))*(1/(m:ℝ)) := by
              rw [one_div, mul_inv, one_div, one_div]
            have h2 : (V:ℝ)/((e:ℝ)*(m:ℝ)) = ((V:ℝ)/(e:ℝ))/(m:ℝ) :=
              (div_div _ _ _).symm
            rw [h1, h2]
            ring
          rw [hinner]
          have hcore := coreSum_le_of_le K h2 (V/e) ((V:ℝ)/(e:ℝ)) hMe
          have hcnn : (0:ℝ) ≤ (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) :=
            mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (by positivity)
          calc (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) *
                  (∑ m ∈ Finset.Icc 1 (V/e), (1/(m:ℝ)) *
                    (Real.log (2 + ((V:ℝ)/(e:ℝ))/(m:ℝ)))^(-2:ℝ))
              ≤ (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) * K :=
                mul_le_mul_of_nonneg_left hcore hcnn
            _ ≤ (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) * (max K 0) :=
                mul_le_mul_of_nonneg_left (le_max_left K 0) hcnn
      _ = (∑ e ∈ Finset.Icc 1 V, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ))) * (max K 0) := by
          rw [Finset.sum_mul]
      _ = (max K 0) * ∑ e ∈ Finset.Icc 1 V, (e.divisors.card : ℝ)/Real.sqrt (e:ℝ) * (1/(e:ℝ)) := by
          rw [mul_comm]
      _ = (max K 0) * ∑ e ∈ Finset.Icc 1 V, (e.divisors.card : ℝ)/((e:ℝ)^(3/2:ℝ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro e he
          exact card_div_sqrt_mul_inv e (Finset.mem_Icc.mp he).1
      _ ≤ (max K 0) * 16 := mul_le_mul_of_nonneg_left (h3 V) hK'0
  refine le_trans key ?_
  rw [mul_comm]
  exact le_max_right _ _


/-- The bookkeeping lemma: the squared `σ_{-1/2}`-weighted sum with a log-power saving is `O(1)`. -/
theorem dyadic_decay_sigma_half_sq : ∃ C : ℝ, 0 < C ∧ ∀ (V : ℕ) (A : ℝ), 1 ≤ A →
    (∑ δ ∈ Finset.Icc 1 V, ((ArithmeticFunction.moebius δ : ℝ)^2) * (Nat.totient δ : ℝ) / ((δ : ℝ)^2) *
        (∑ d ∈ δ.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ^ 2 *
        (Real.log (2 + (V : ℝ) / (δ : ℝ))) ^ (-2 * A)) ≤ C := by
  obtain ⟨K, hK⟩ := core_dyadic_sum_bound
  exact dyadic_decay_sigma_half_sq_of K sigma_half_sq_divisor_bound hK tau_rpow_sum_bound

end Work.LinnikAreas.Density4
