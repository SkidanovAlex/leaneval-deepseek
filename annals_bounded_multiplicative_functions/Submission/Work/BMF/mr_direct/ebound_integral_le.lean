import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime
import Submission.Work.BMF.mr_direct.card_diff_natIcc_le
import Submission.Work.BMF.mr_direct.mv_natIcc_mean_value
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.ebound_eq_fiber_sum
import Submission.Work.BMF.mr_direct.ebD_norm_sq_le_one
import Submission.Work.BMF.mr_direct.pSetB_mem_range
import Submission.Work.BMF.mr_direct.ebD_sum_div_sq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators

-- Mean-square bound for the range-extension error `ebound`.
-- `hC₀` is the Montgomery–Vaughan large-sieve mean value theorem
-- (`Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`), unpacked.
-- Suggested route: write `ebound b c K P Q X t` as `Σ_{i ∈ pSetB K P Q X} γ i · (nn i)^{-(1+it)}`
-- with `nn ⟨p,m⟩ = p*m`, merge equal frequencies via `Finset.sum_fiberwise_of_maps_to`, and apply
-- `Work.BMF.mrDirect.mv_natIcc_mean_value C₀ hC₀` (already proved in this workspace) to the merged
-- polynomial; then bound `#fiber * Σ_{fiber}‖γ‖² ≤ 1` for every `n`
-- (using `omegaCount_mul_prime`: for `p ∈ primeSet P Q`, `p ∣ n`, the denominators satisfy
-- `omegaCount P Q (n/p) + 1 ≥ omegaCount P Q n =: r`, each `‖γ‖ ≤ 1/r` and `#fiber ≤ r`),
-- and finally the support (`m ∉ natIcc (X/p) (2*X/p)` forces `p*m ∉ natIcc X (2*X)`) together
-- with `card_diff_natIcc_le`.
theorem ebound_integral_le (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2)
    (b c : ℕ → ℂ) (K P Q X S : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (hS : 0 ≤ S) :
    (∫ t in (-S)..S, ‖Work.BMF.mrDirect.ebound b c K P Q X t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          ((8 * X / K + 8) * Real.exp 2 / X ^ 2) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hNA : 0 < X * Real.exp (-(1 / K)) := by positivity
  have hAB : X * Real.exp (-(1 / K)) ≤ 2 * X * Real.exp (1 / K) := by
    have h1 : Real.exp (-(1 / K)) ≤ Real.exp (1 / K) :=
      Real.exp_le_exp.mpr (by
        have h : 0 ≤ 1 / K := by positivity
        linarith)
    have h2 : 0 < Real.exp (1 / K) := Real.exp_pos _
    calc X * Real.exp (-(1 / K)) ≤ X * Real.exp (1 / K) :=
          mul_le_mul_of_nonneg_left h1 hXpos.le
      _ ≤ 2 * X * Real.exp (1 / K) := by nlinarith [mul_pos hXpos h2]
  -- the range of the products `p * m`, `(p,m) ∈ pSetB`
  have hrange : ∀ i ∈ Work.BMF.mrDirect.pSetB K P Q X,
      ebnn i ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) ∧
        ebnn i ∉ Work.BMF.natIcc X (2 * X) :=
    fun i hi => pSetB_mem_range K P Q X hX hK i hi
  -- `ebound` is the merged Dirichlet polynomial
  have heq : ∀ t : ℝ, Work.BMF.mrDirect.ebound b c K P Q X t
      = ∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
          ebD b c K P Q X n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) :=
    fun t => ebound_eq_fiber_sum b c K P Q X t
      (Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)))
      (fun i hi => (hrange i hi).1)
  have hint : (∫ t in (-S)..S, ‖Work.BMF.mrDirect.ebound b c K P Q X t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
            ebD b c K P Q X n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrArg (fun z => ‖z‖ ^ 2) (heq t)
  -- Montgomery–Vaughan mean value theorem for the merged polynomial
  have hmv := mv_natIcc_mean_value C₀ hC₀ (ebD b c K P Q X)
    (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)) S hNA hAB hS
  -- the merged coefficients have energy at most one, and their support is small
  have hsum := ebD_sum_div_sq_le b c K P Q X hX hK
    (ebD_norm_sq_le_one b c K P Q X hX hP hPQ hb hc) hrange
  have hcoef : 0 ≤ 2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K)) := by
    have hC0nn : 0 ≤ C₀ := c0_nonneg_of_mv C₀ hC₀
    have hBnn : 0 ≤ 2 * X * Real.exp (1 / K) := by positivity
    have h3 : 0 ≤ 3 * C₀ * (2 * X * Real.exp (1 / K)) :=
      mul_nonneg (mul_nonneg (by norm_num) hC0nn) hBnn
    linarith
  calc (∫ t in (-S)..S, ‖Work.BMF.mrDirect.ebound b c K P Q X t‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
            ebD b c K P Q X n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          ∑ n ∈ Work.BMF.natIcc (X * Real.exp (-(1 / K))) (2 * X * Real.exp (1 / K)),
            ‖ebD b c K P Q X n‖ ^ 2 / (n : ℝ) ^ 2 := hmv
    _ ≤ (2 * S + 3 * C₀ * (2 * X * Real.exp (1 / K))) *
          ((8 * X / K + 8) * Real.exp 2 / X ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hcoef

end Work.BMF.mr_direct
