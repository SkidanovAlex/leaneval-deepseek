import Mathlib
import Submission.Commons.NumberTheory.Totient.smooth_inv_sum_le_totient_ratio
import Submission.Work.LinnikAreas.Density4.sHalf_facts

namespace Work.LinnikAreas.Density4.KappaSum

open Finset BigOperators

noncomputable section

/-- The per-prime ratio `(p/(p-1)) / (1 + 1/√p)`.  It is `4 - 2√2 < 3/2` at `p = 2`
and `≤ 1` at every odd prime, so the product of these ratios over any finite set of
primes is `< 3/2`; that is the only content of the Euler-product comparison. -/
private def primeRatio (p : ℕ) : ℝ :=
  ((p : ℝ) / ((p : ℝ) - 1)) / (1 + 1 / Real.sqrt (p : ℝ))

private lemma primeRatio_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ primeRatio p := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hs : (0 : ℝ) < Real.sqrt (p : ℝ) := by
    apply Real.sqrt_pos.mpr
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hd : (0 : ℝ) < 1 + 1 / Real.sqrt (p : ℝ) := by positivity
  exact div_nonneg (div_nonneg (by positivity) (le_of_lt hp1)) (le_of_lt hd)

/-- At every odd prime the ratio is `≤ 1`, because `√p ≤ p - 1` for `p ≥ 3`. -/
private lemma primeRatio_le_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : primeRatio p ≤ 1 := by
  have hp2le : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2le
    linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2le
    linarith
  have hsq : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
  have hden : (0 : ℝ) < 1 + 1 / Real.sqrt (p : ℝ) := by positivity
  have hkey : Real.sqrt (p : ℝ) ≤ (p : ℝ) - 1 := by
    have hs := Real.sq_sqrt (le_of_lt hpR)
    have hnn := Real.sqrt_nonneg (p : ℝ)
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    nlinarith [hs, hnn, h3]
  rw [primeRatio, div_le_one hden, div_le_iff₀ hpm1]
  have h1 : (1 + 1 / Real.sqrt (p : ℝ)) * ((p : ℝ) - 1)
      = ((p : ℝ) - 1) + ((p : ℝ) - 1) / Real.sqrt (p : ℝ) := by
    ring
  rw [h1]
  have h2 : (1 : ℝ) ≤ ((p : ℝ) - 1) / Real.sqrt (p : ℝ) := by
    rw [le_div_iff₀ hsq]
    simpa using hkey
  linarith

/-- At `p = 2` the ratio is `2/(1 + 1/√2) = 4 - 2√2 ≤ 3/2`, i.e. `√2 ≤ 3`. -/
private lemma primeRatio_two_le : primeRatio 2 ≤ 3 / 2 := by
  have hsqpos : (0 : ℝ) < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqle : Real.sqrt (2 : ℝ) ≤ 3 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith [h, hnn]
  have h2 : (1 : ℝ) / 3 ≤ 1 / Real.sqrt 2 := one_div_le_one_div_of_le hsqpos hsqle
  have h4 : (4 : ℝ) / 3 ≤ 1 + 1 / Real.sqrt 2 := by
    have := add_le_add_left h2 1
    linarith
  have key : (2 : ℝ) ≤ 3 / 2 * (1 + 1 / Real.sqrt (2 : ℝ)) := by
    calc (2 : ℝ) = 3 / 2 * (4 / 3) := by norm_num
      _ ≤ 3 / 2 * (1 + 1 / Real.sqrt 2) := mul_le_mul_of_nonneg_left h4 (by norm_num)
  have hpos : (0 : ℝ) < 1 + 1 / Real.sqrt (2 : ℝ) := by positivity
  rw [primeRatio]
  simp only [Nat.cast_ofNat]
  rw [div_le_iff₀ hpos]
  norm_num
  simpa using key

/-- `∏_{p ∈ S} p/(p-1) ≤ 2 · ∏_{p ∈ S} (1 + p^{-1/2})` for every finite set `S` of
primes.  Writing each factor as `primeRatio p · (1 + p^{-1/2})`, the product of the
ratios is at most `3/2` (every ratio is `≤ 1` except at `p = 2`, where it is `≤ 3/2`). -/
private lemma prod_primeRatio_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, primeRatio p ≤ 2 := by
  by_cases h2 : 2 ∈ S
  · have hsplit : ∏ p ∈ S, primeRatio p = primeRatio 2 * ∏ p ∈ S.erase 2, primeRatio p := by
      rw [← Finset.mul_prod_erase S primeRatio h2]
    have hrest : ∏ p ∈ S.erase 2, primeRatio p ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        obtain ⟨hpne, hpS⟩ := Finset.mem_erase.mp hp
        exact primeRatio_nonneg (hS p hpS).two_le
      · intro p hp
        obtain ⟨hpne, hpS⟩ := Finset.mem_erase.mp hp
        exact primeRatio_le_one (hS p hpS) hpne
    have hnn : 0 ≤ ∏ p ∈ S.erase 2, primeRatio p :=
      Finset.prod_nonneg (fun p hp => primeRatio_nonneg (hS p (Finset.mem_erase.mp hp).2).two_le)
    rw [hsplit]
    calc primeRatio 2 * ∏ p ∈ S.erase 2, primeRatio p
        ≤ (3 / 2) * 1 := mul_le_mul primeRatio_two_le hrest hnn (by norm_num)
      _ ≤ 2 := by norm_num
  · have hle1 : ∏ p ∈ S, primeRatio p ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro p hp
        exact primeRatio_nonneg (hS p hp).two_le
      · intro p hp
        exact primeRatio_le_one (hS p hp) (fun h => h2 (h ▸ hp))
    linarith

/-- `r/φ(r) ≤ 2·σ_{-1/2}(r)` where `σ_{-1/2}(r) = Σ_{d | r} d^{-1/2}`.
Route: `r/φ(r) = ∏_{p | r} p/(p-1)` (`Commons.NumberTheory.Totient.totient_div_eq_prod_primeFactors_div_pred`),
and `Σ_{d | r} d^{-1/2} ≥ Σ_{d | r} μ(d)² d^{-1/2} = ∏_{p | r} (1 + p^{-1/2})`
(`Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors`); so it suffices to compare the
two products. Per prime, `(p/(p-1))/(1+1/√p) ≤ 1` for `p ≥ 3` and `= 1.1716…  ≤ 3/2` for `p = 2`, so the
product of ratios over `p | r` is at most `3/2 ≤ 2`. -/
theorem div_totient_le_two_mul_sHalf (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) / (Nat.totient r : ℝ) ≤
      2 * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
  have hS : ∀ p ∈ r.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsigma := (Work.LinnikAreas.Density4.sHalf_facts r hr).1
  have hphi := Commons.NumberTheory.Totient.totient_div_eq_prod_primeFactors_div_pred r hr
  have hchain : ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
      ≤ 2 * ∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
    have hratio := prod_primeRatio_le r.primeFactors hS
    have hfac : ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1)
        = (∏ p ∈ r.primeFactors, primeRatio p)
          * ∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
        linarith
      have hden : (1 + 1 / Real.sqrt (p : ℝ)) ≠ 0 := by
        have hs : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
        positivity
      rw [primeRatio, div_mul_cancel₀ _ hden]
    rw [hfac]
    exact mul_le_mul_of_nonneg_right hratio
      (Finset.prod_nonneg (fun p hp => by
        have : (0 : ℝ) < (p : ℝ) := by
          have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
          linarith
        have hs : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr this
        positivity))
  calc (r : ℝ) / (Nat.totient r : ℝ)
      = ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hphi
    _ ≤ 2 * ∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := hchain
    _ ≤ 2 * ∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ) :=
        mul_le_mul_of_nonneg_left hsigma (by norm_num)

end

end Work.LinnikAreas.Density4.KappaSum
