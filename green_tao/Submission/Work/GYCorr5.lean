import Submission.Work.GYCorr4
import Submission.Work.CorrCondGY

/-!
# The correlation condition for the degenerate system: the reduction

This file reduces the Green–Tao correlation condition `CorrCond p ν m₀ C` for the GY majorant
`ν = nuGT` to the *analytic* correlation bound (`hgy`) for the degenerate system
`x ↦ W(x + h_i) + 1`.

The particular shape of `hgy` used here is
`𝔼_x ∏_i ν(x+h_i) ≤ Σ_{i<j} W_m(h_i - h_j)` where the pair weight `W_m` is
* `Dc m` when `h_i = h_j` (Green–Tao's diagonal case, bounded by `‖ν‖_∞^m`),
* `K m · (∏_{q | dist} (1 + q^{-1/2}))^(E m)` otherwise,

with a *free* exponent `E m` and *free* constants `K m`, `Dc m` (this freedom is what makes the
`G_0`/`G_1` bookkeeping of Green–Tao's Proposition GY2 work out).
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace Corr

/-- The pointwise pair weight of the correlation bound for the degenerate system. -/
noncomputable def corrWeight (p : ℕ) [Fact p.Prime] (K Dc : ℕ → ℝ) (E : ℕ → ℕ) (m : ℕ)
    (x : ZMod p) : ℝ :=
  if min x.val (p - x.val) = 0 then Dc m
  else K m * (∏ q ∈ (min x.val (p - x.val)).primeFactors,
      (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m)

lemma corrWeight_nonneg {p : ℕ} [Fact p.Prime] {K Dc : ℕ → ℝ} (hK : ∀ m, 0 ≤ K m)
    (hDc : ∀ m, 0 ≤ Dc m) (E : ℕ → ℕ) (m : ℕ) (x : ZMod p) :
    0 ≤ corrWeight p K Dc E m x := by
  rw [corrWeight]
  split
  · exact hDc m
  · refine mul_nonneg (hK m) (pow_nonneg ?_ _)
    exact Finset.prod_nonneg fun q _ => by
      have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ)) (-(1 / 2 : ℝ))
      linarith

/-- The bracket of the `hgy` hypothesis is exactly the pair weight. -/
lemma corrWeight_bracket {p : ℕ} [Fact p.Prime] {K Dc : ℕ → ℝ} (E : ℕ → ℕ) (m : ℕ)
    (h : Fin m → ZMod p) (i j : Fin m) :
    (if h i = h j then Dc m
     else K m * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
             (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m))
      = corrWeight p K Dc E m (h i - h j) := by
  by_cases heq : h i = h j
  · rw [if_pos heq, corrWeight]
    have hx0 : h i - h j = 0 := by rw [heq, sub_self]
    rw [hx0, ZMod.val_zero, Nat.sub_zero, if_pos (by simp)]
  · rw [if_neg heq, corrWeight]
    have hxne : h i - h j ≠ 0 := sub_ne_zero.mpr heq
    have hmin : min (h i - h j).val (p - (h i - h j).val) ≠ 0 := by
      intro h0
      rcases Nat.min_eq_zero_iff.mp h0 with hv | hv
      · exact hxne ((ZMod.val_eq_zero _).mp hv)
      · have hlt := ZMod.val_lt (h i - h j)
        omega
    rw [if_neg hmin]

/-- **The correlation condition from the analytic bound for the degenerate system.** -/
theorem corrCond_of_gy_ub {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (ν : ZMod p → ℝ) (m₀ : ℕ)
    {K Dc : ℕ → ℝ} (hK : ∀ m, 0 ≤ K m) (hDc : ∀ m, 0 ≤ Dc m) {E : ℕ → ℕ}
    (hgy : ∀ m, 1 < m → m ≤ m₀ → ∀ h : Fin m → ZMod p,
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i, ν (x + h i)
        ≤ ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            (if h i = h j then Dc m
             else K m * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                     (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m))) :
    ∃ C : ℕ → ℕ → ℝ, Commons.NumberTheory.Sieve.CorrCond p ν m₀ C := by
  classical
  refine ⟨fun m q => max 1 ((p : ℝ)⁻¹ * ∑ x : ZMod p, (corrWeight p K Dc E m x) ^ q), ?_⟩
  intro m hm1 hm2
  refine ⟨corrWeight p K Dc E m, ?_, ?_, ?_⟩
  · intro x
    exact corrWeight_nonneg hK hDc E m x
  · intro q hq
    rw [ZMod.card p]
    exact le_max_right (1 : ℝ) _
  · intro h
    have hkey := hgy m hm1 hm2 h
    have hRHS : (∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          (if h i = h j then Dc m
           else K m * (∏ q ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                   (1 + (q : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (E m)))
        = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            corrWeight p K Dc E m (h i - h j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact corrWeight_bracket E m h i j
    rw [ZMod.card p, ← hRHS]
    exact hkey

end Corr
end GYMaj
