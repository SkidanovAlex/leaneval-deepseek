import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs

/-!
# `ZAc_gcdsum`: the `ZAc` weight sum with the `(r₁,r₂)`-gcd weight

This is the "arithmetic core" step advertised in `ZAc_bound`: the four-fold sum
`ZAc R h₁ h₂ thr` is bounded by a *double* sum over the pairs `(r₁,r₂)`, each pair weighted by
`1 + (r₁,r₂)·(2R+1)/|r₁|` and by `τ(Re Λ)⁴`.  The content of the present lemma is that this
double sum over the *axis-avoiding* pairs (`|r₁|,|r₂| > thr = √(ϑN)`) is bounded by
`C ϑ^{-1/2} · UB R h₁ h₂`, where `UB R h₁ h₂ = Σ_{(u₁,u₂) ∈ I²} (u₁,u₂)·τ(u₁h₁²−u₂h₂²)⁴`
is the *full* double sum (no threshold indicator, no `1 +`).

Mathematically (*FI* §9): on the surviving range `thr < |r₁|`,

* `(2R+1)/|r₁| ≤ 8 √N / √(ϑN) = 8 ϑ^{-1/2}` (using `2R+1 ≤ 8√N` and `thr = √(ϑN)`), and
* `1 ≤ ϑ^{-1/2}·(r₁,r₂)` (since `0 < ϑ ≤ 1` and `r₁ ≠ 0`, so `(r₁,r₂) ≥ 1`),

so the weight `1 + (r₁,r₂)(2R+1)/|r₁|` is at most `9 ϑ^{-1/2}(r₁,r₂)`.  Summing over the box and
dropping the threshold indicator (which only makes the full sum larger) gives the claim with the
absolute constant `C = 9`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Per-pair estimate.**  For `0 < ϑ ≤ 1`, `thr = √(ϑN)` and `2R+1 ≤ 8√N`, the
axis-avoiding pair weight is dominated by `9 ϑ^{-1/2}` times the `UB`-summand
`(r₁,r₂)·τ(Re Λ)⁴`. -/
private lemma ZAc_pair_le (R : ℤ) (h1 h2 : ℤ) (thr Nr ϑ : ℝ)
    (hϑpos : 0 < ϑ) (hϑle : ϑ ≤ 1) (hNr : 1 ≤ Nr)
    (hthr : thr = Real.sqrt (ϑ * Nr))
    (h2R : (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr)
    (r1 r2 : ℤ) :
    (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
        (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
          * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4)
      else 0)
      ≤ 9 * ϑ ^ (-(1:ℝ)/2) * ((Nat.gcd r1.natAbs r2.natAbs : ℝ)
          * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4)) := by
  by_cases hc : thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)|
  · rw [if_pos hc]
    set τ : ℝ := ((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ) with hτdef
    have hτ4 : 0 ≤ τ^4 := by positivity
    have hg : ((r1.gcd r2 : ℕ) : ℝ) = (Nat.gcd r1.natAbs r2.natAbs : ℝ) := by
      rw [Int.gcd_eq_natAbs]
    rw [hg]
    set g : ℝ := (Nat.gcd r1.natAbs r2.natAbs : ℝ) with hgdef
    have hg_nonneg : 0 ≤ g := by positivity
    have hthr0 : 0 ≤ thr := by rw [hthr]; exact Real.sqrt_nonneg _
    have hr1pos : 0 < |(r1:ℝ)| := lt_of_le_of_lt hthr0 hc.1
    have hr1ne : r1 ≠ 0 := by
      intro h; rw [h] at hr1pos; simp at hr1pos
    have hg1 : 1 ≤ g := by
      rw [hgdef]
      have hp : 0 < Nat.gcd r1.natAbs r2.natAbs :=
        Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hr1ne)
      have h1n : (1:ℕ) ≤ Nat.gcd r1.natAbs r2.natAbs := hp
      exact_mod_cast h1n
    have he : -(1:ℝ)/2 ≤ 0 := by norm_num
    have hϑe_pos : 0 < ϑ ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hϑpos _
    have hϑe_ge1 : 1 ≤ ϑ ^ (-(1:ℝ)/2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hϑpos hϑle he
    have hpe : ϑ ^ (-(1:ℝ)/2) * Real.sqrt (ϑ * Nr) = Real.sqrt Nr := by
      rw [Real.sqrt_mul (le_of_lt hϑpos) Nr, ← mul_assoc]
      rw [show ϑ ^ (-(1:ℝ)/2) * Real.sqrt ϑ = 1 from by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hϑpos]
        have : -(1:ℝ)/2 + 1/2 = 0 := by norm_num
        rw [this, Real.rpow_zero]]
      rw [one_mul]
    have hlt0 : Real.sqrt (ϑ * Nr) < |(r1:ℝ)| := by rw [← hthr]; exact hc.1
    have hlt1 : ϑ ^ (-(1:ℝ)/2) * Real.sqrt (ϑ*Nr) < ϑ ^ (-(1:ℝ)/2) * |(r1:ℝ)| :=
      mul_lt_mul_of_pos_left hlt0 hϑe_pos
    have hlt : Real.sqrt Nr < ϑ ^ (-(1:ℝ)/2) * |(r1:ℝ)| := by rw [← hpe]; exact hlt1
    have h8 : 2*(R:ℝ)+1 < 8*(ϑ ^ (-(1:ℝ)/2) * |(r1:ℝ)|) :=
      lt_of_le_of_lt h2R (mul_lt_mul_of_pos_left hlt (by norm_num))
    have hdiv : (2*(R:ℝ)+1)/|(r1:ℝ)| ≤ 8*ϑ^(-(1:ℝ)/2) := by
      have h8le : 2*(R:ℝ)+1 ≤ 8*(ϑ^(-(1:ℝ)/2) * |(r1:ℝ)|) := le_of_lt h8
      have h := div_le_div_of_nonneg_right h8le (le_of_lt hr1pos)
      have heq : (8*(ϑ^(-(1:ℝ)/2) * |(r1:ℝ)|))/|(r1:ℝ)| = 8*ϑ^(-(1:ℝ)/2) := by
        rw [mul_div_assoc, mul_div_assoc, div_self (ne_of_gt hr1pos), mul_one]
      rwa [heq] at h
    have hstep : g * (2*(R:ℝ)+1)/|(r1:ℝ)| ≤ g * (8*ϑ^(-(1:ℝ)/2)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hdiv hg_nonneg
    have hone : 1 ≤ ϑ^(-(1:ℝ)/2) * g := by
      have := mul_le_mul hϑe_ge1 hg1 (zero_le_one) (le_of_lt hϑe_pos)
      simpa using this
    have hscal : 1 + g * (2*(R:ℝ)+1)/|(r1:ℝ)| ≤ 9 * (ϑ^(-(1:ℝ)/2) * g) := by
      calc 1 + g * (2*(R:ℝ)+1)/|(r1:ℝ)|
          ≤ 1 + g*(8*ϑ^(-(1:ℝ)/2)) := add_le_add le_rfl hstep
        _ ≤ ϑ^(-(1:ℝ)/2)*g + 8*ϑ^(-(1:ℝ)/2)*g :=
            add_le_add hone (le_of_eq (by ring))
        _ = 9*(ϑ^(-(1:ℝ)/2)*g) := by ring
    calc (1 + g * (2*(R:ℝ)+1)/|(r1:ℝ)|) * τ^4
        ≤ (9*(ϑ^(-(1:ℝ)/2)*g)) * τ^4 := mul_le_mul_of_nonneg_right hscal hτ4
      _ = 9 * ϑ^(-(1:ℝ)/2) * (g*τ^4) := by ring
  · rw [if_neg hc]
    positivity

theorem ZAc_gcdsum :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (h1 h2 : ℤ) (thr Nr ϑ : ℝ),
      0 < ϑ → ϑ ≤ 1 → 1 ≤ Nr → 0 ≤ R → thr = Real.sqrt (ϑ * Nr) →
      (2 * (R : ℝ) + 1) ≤ 8 * Real.sqrt Nr →
      (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
          (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4)
        else 0))
        ≤ C * ϑ ^ (-(1 : ℝ) / 2) * UB R h1 h2 := by
  refine ⟨9, by norm_num, ?_⟩
  intro R h1 h2 thr Nr ϑ hϑpos hϑle hNr h0R hthr h2R
  have hsum :
      (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if thr < |(r1 : ℝ)| ∧ thr < |(r2 : ℝ)| then
          (1 + ((r1.gcd r2 : ℕ) : ℝ) * (2 * (R : ℝ) + 1) / |(r1 : ℝ)|)
            * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4)
        else 0))
      ≤ ∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (9 * ϑ ^ (-(1:ℝ)/2) * ((Nat.gcd r1.natAbs r2.natAbs : ℝ)
            * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4))) := by
    apply Finset.sum_le_sum; intro r1 _
    apply Finset.sum_le_sum; intro r2 _
    exact ZAc_pair_le R h1 h2 thr Nr ϑ hϑpos hϑle hNr hthr h2R r1 r2
  have hfac :
      (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (9 * ϑ ^ (-(1:ℝ)/2) * ((Nat.gcd r1.natAbs r2.natAbs : ℝ)
            * ((((tA h1 h2 r1 r2).natAbs.divisors.card : ℝ)) ^ 4))))
      = 9 * ϑ ^ (-(1:ℝ)/2) * UB R h1 h2 := by
    rw [UB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r1 _
    rw [Finset.mul_sum]
  exact le_trans hsum (le_of_eq hfac)

end

end Work.FIArea2.Count
