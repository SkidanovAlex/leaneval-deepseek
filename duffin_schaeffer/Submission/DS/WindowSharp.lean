import Mathlib
import Submission.Commons.NumberTheory.Totient.selberg_window_count_le
import Submission.Commons.NumberTheory.Totient.selberg_VQ_ge_sharp

open Finset
open scoped BigOperators

/-!
# The coprime-window density bound with constant `17`

Session (2026-10-07).  `Commons.NumberTheory.Windows.window_density_le` gives

    #{c ≤ y : (c,P)=1} ≤ 25·y·∏_{p|P}(1−1/p)

for squarefree `P` with all prime factors `≤ y`, by splitting at `Q := ∏(1−1/p) ≥ 1/25`
(trivial bound) resp. applying the Selberg sieve bound
`#window ≤ y/V + (4√y/V)²`, `V = ∑_{d|P,d≤√y}1/φ(d)`, together with `V·Q ≥ 1/5`.

Here we redo the same computation with the **sharp Rankin bound** `V·Q ≥ 7/25`
(`Commons.NumberTheory.Totient.selberg_VQ_ge_sharp`), obtaining the constant `17`
in place of `25` — the constant needed by the (b)-front's residual
(`psiFree_lower_half_small`): with `K = 17` the per-window bound closes Regime II
whenever the weighted average `E_w[h] = Σ_t (w_t/W)·∏_{p|n,⌊C/r_t⌋<p≤C}p/(p−1)`
satisfies `K·E_w[h] ≤ 25·δ`.

The numerical arithmetic of the split: with `c₀ = 7/25`, in the complementary case
`Q < 1/17` one has `V ≥ c₀/Q`, so

    #window ≤ (1/c₀ + 16Q/c₀²)·y·Q ≤ (25/7 + 16/(17·(7/25)²))·y·Q
            = (3.5714… + 12.1656…)·y·Q < 15.74·y·Q ≤ 17·y·Q.
-/

namespace Submission.DS

/-- **Coprime-window density bound with constant `17`.** -/
theorem window_density_le_17 (P y : ℕ) (hP : Squarefree P)
    (hy : ∀ p ∈ P.primeFactors, p ≤ y) :
    (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ) ≤
      17 * (y : ℝ) * ∏ p ∈ P.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hQeq : ∏ p ∈ P.primeFactors, (1 - (1 : ℝ) / (p : ℝ))
      = ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl; intro p _; rw [one_div]
  rw [hQeq]
  rcases Nat.eq_zero_or_pos y with hy0 | hypos
  · subst hy0
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by norm_num)]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
    norm_num
  · have hy1 : 1 ≤ y := hypos
    set V : ℝ := ∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0 with hV
    set Q : ℝ := ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) with hQ
    have hVge1 : 1 ≤ V := by
      rw [hV]
      have h1mem : 1 ∈ P.divisors := by
        rw [Nat.mem_divisors]; exact ⟨one_dvd P, hP.ne_zero⟩
      have h1z : (1:ℕ) ≤ Nat.sqrt y := by rw [Nat.le_sqrt]; omega
      calc (1:ℝ) = (Nat.totient 1 : ℝ)⁻¹ := by simp
        _ = (if (1:ℕ) ≤ Nat.sqrt y then (Nat.totient 1 : ℝ)⁻¹ else 0) := by rw [if_pos h1z]
        _ ≤ ∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0 :=
            Finset.single_le_sum (f := fun d => if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0)
              (by intro d _; positivity) h1mem
    have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hVge1
    have hVQ : (7:ℝ)/25 ≤ V * Q := by
      have := Commons.NumberTheory.Totient.selberg_VQ_ge_sharp P y hP hy1 hy
      rwa [← hV, ← hQ] at this
    have hsel := Commons.NumberTheory.Totient.selberg_window_count_le P y hP hy1
    rw [← hV] at hsel
    have hQnn : 0 ≤ Q := by
      rw [hQ]; apply Finset.prod_nonneg; intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by
        exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ (by linarith)
    by_cases hQc : (1:ℝ)/17 ≤ Q
    · have hNle : (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ) ≤ (y:ℝ) := by
        have h2 : ((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card ≤ (Finset.Icc 1 y).card :=
          Finset.card_filter_le _ _
        have h3 : (Finset.Icc 1 y).card = y := by rw [Nat.card_Icc]; omega
        rw [h3] at h2
        exact_mod_cast h2
      have : (y:ℝ) ≤ 17 * (y:ℝ) * Q := by
        have hy0' : (0:ℝ) ≤ (y:ℝ) := by positivity
        nlinarith [hQc]
      linarith [hNle, this]
    · have hQlt : Q < 1/17 := lt_of_not_ge hQc
      -- `7 ≤ 25·(V·Q)` from `7/25 ≤ V·Q`
      have h7 : (7:ℝ) ≤ 25 * (V * Q) := by nlinarith [hVQ]
      -- `1/V ≤ 25Q/7`
      have hVinv : (1:ℝ)/V ≤ 25*Q/7 := by
        rw [div_le_iff₀ hVpos]
        rw [div_mul_eq_mul_div]
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 7)]
        nlinarith [h7, mul_comm V Q]
      -- `(4√y/V)² ≤ 16·(25Q/7)²·y`
      have hsq : (4 * (Nat.sqrt y : ℝ) / V)^2 ≤ 16 * (25*Q/7)^2 * (y:ℝ) := by
        have hle : 4 * (Nat.sqrt y : ℝ) / V ≤ 4 * (Nat.sqrt y : ℝ) * (25*Q/7) := by
          have h := mul_le_mul_of_nonneg_left hVinv (by positivity : (0:ℝ) ≤ 4 * (Nat.sqrt y : ℝ))
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
        have hle2 : (4 * (Nat.sqrt y : ℝ) * (25*Q/7))^2 = 16 * (25*Q/7)^2 * (Nat.sqrt y : ℝ)^2 := by ring
        have hs : (Nat.sqrt y : ℝ)^2 ≤ (y:ℝ) := by exact_mod_cast Nat.sqrt_le' y
        have hsq' : (4 * (Nat.sqrt y : ℝ) / V)^2 ≤ (4 * (Nat.sqrt y : ℝ) * (25*Q/7))^2 := by
          have := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 4 * (Nat.sqrt y : ℝ) / V) hle
          simpa [sq] using this
        calc (4 * (Nat.sqrt y : ℝ) / V)^2 ≤ (4 * (Nat.sqrt y : ℝ) * (25*Q/7))^2 := hsq'
          _ = 16 * (25*Q/7)^2 * (Nat.sqrt y : ℝ)^2 := hle2
          _ ≤ 16 * (25*Q/7)^2 * (y:ℝ) := by
              have h0 : (0:ℝ) ≤ 16 * (25*Q/7)^2 := by positivity
              exact mul_le_mul_of_nonneg_left hs h0
      have hyV : (y:ℝ)/V ≤ 25*Q/7*(y:ℝ) := by
        have h := mul_le_mul_of_nonneg_left hVinv (by positivity : (0:ℝ) ≤ (y:ℝ))
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
      calc (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ)
          ≤ (y:ℝ)/V + (4 * (Nat.sqrt y : ℝ)/V)^2 := hsel
        _ ≤ 25*Q/7*(y:ℝ) + 16*(25*Q/7)^2*(y:ℝ) := by linarith [hyV, hsq]
        _ = (y:ℝ) * ((25/7)*Q + 16*(25/7)^2*Q^2) := by ring
        _ ≤ (y:ℝ) * (17*Q) := by
            have h2 : (25/7:ℝ)*Q + 16*(25/7)^2*Q^2 ≤ 17*Q := by
              nlinarith [hQlt, hQnn]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 17 * (y:ℝ) * Q := by ring

end Submission.DS
