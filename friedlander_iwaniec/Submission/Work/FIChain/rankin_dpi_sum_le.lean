import Mathlib
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false

namespace Work.FIChain

open Finset

/-! ## Rankin's trick for the `Δπ`-tail of the `Π`-subset sum

The companion's §10 estimates the `n₁ > Δπ` part of the `n`-sum by Rankin's trick.  This file
provides the elementary combinatorial inequality behind it, together with the arithmetic input
`Dpi x κ ≥ exp(κ (log log x)³)` that converts the Rankin factor `(Dpi x κ)^{-δ}` into a factor
`(log x)^{-κ/2}` for the choice `δ = 1/(2 (log log x)²)`.

The main theorem `rankin_dpi_sum_le` bounds the `∏_{p ∈ S} 2^k/p`-weighted sum over those
subsets `S` of the primes `≤ Pz` whose product exceeds `Δπ`. -/

/-- **Rankin's trick, subset form.**  For a finite set `s` of positive integers, a threshold
`T > 0`, an exponent `δ ≥ 0` and a weight factor `C ≥ 0`,
```
∑_{S : T < ∏_{p∈S} p} ∏_{p∈S} C/p  ≤  T^{-δ} · ∏_{p∈s} (1 + C p^{δ-1}).
```
On the filtered range `∏_{p∈S} p > T` we insert the factor
`(∏_{p∈S} p)^δ / T^δ ≥ 1`; the resulting sum is then the complete Euler product over `s`. -/
private lemma rankin_powerset_sum_le_aux
    (s : Finset ℕ) (T δ C : ℝ) (hT : 0 < T) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hp : ∀ p ∈ s, 0 < (p : ℝ)) :
    (∑ S ∈ s.powerset.filter (fun S : Finset ℕ => T < ∏ p ∈ S, (p : ℝ)),
        ∏ p ∈ S, C / (p : ℝ))
      ≤ T ^ (-δ) * ∏ p ∈ s, (1 + C * (p : ℝ) ^ (δ - 1)) := by
  classical
  have h1 : (∑ S ∈ s.powerset.filter (fun S : Finset ℕ => T < ∏ p ∈ S, (p : ℝ)),
        ∏ p ∈ S, C / (p : ℝ))
      ≤ ∑ S ∈ s.powerset.filter (fun S : Finset ℕ => T < ∏ p ∈ S, (p : ℝ)),
        T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)) := by
    apply Finset.sum_le_sum
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨hSsub, hSgt⟩ := hS
    have hSsub' : S ⊆ s := Finset.mem_powerset.mp hSsub
    have hpos : ∀ p ∈ S, 0 < (p : ℝ) := fun p hp' => hp p (hSsub' hp')
    have hpow : T ^ δ ≤ (∏ p ∈ S, (p : ℝ)) ^ δ :=
      Real.rpow_le_rpow hT.le (le_of_lt hSgt) hδ
    have hTd_pos : 0 < T ^ δ := Real.rpow_pos_of_pos hT δ
    have hge1 : 1 ≤ (∏ p ∈ S, (p : ℝ)) ^ δ * T ^ (-δ) := by
      rw [Real.rpow_neg hT.le δ, ← div_eq_mul_inv, le_div_iff₀ hTd_pos]
      simpa using hpow
    have hg_nonneg : 0 ≤ ∏ p ∈ S, C / (p : ℝ) :=
      Finset.prod_nonneg (fun p hp' => div_nonneg hC (le_of_lt (hpos p hp')))
    have hprod : (∏ p ∈ S, (p : ℝ) ^ δ) * (∏ p ∈ S, C / (p : ℝ))
        = ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp'
      rw [div_eq_mul_inv, show δ - 1 = δ + (-1) by ring,
        Real.rpow_add (hpos p hp') δ (-1), ← Real.rpow_neg_one (p : ℝ)]
      ring
    have hPS : (∏ p ∈ S, (p : ℝ)) ^ δ = ∏ p ∈ S, (p : ℝ) ^ δ :=
      (Real.finsetProd_rpow S (fun p => (p : ℝ)) (fun p hp' => le_of_lt (hpos p hp')) δ).symm
    have key : ((∏ p ∈ S, (p : ℝ) ^ δ) * T ^ (-δ)) * (∏ p ∈ S, C / (p : ℝ))
        = T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)) := by
      rw [mul_comm (∏ p ∈ S, (p : ℝ) ^ δ) (T ^ (-δ)), mul_assoc, hprod]
    calc ∏ p ∈ S, C / (p : ℝ)
        = 1 * ∏ p ∈ S, C / (p : ℝ) := (one_mul _).symm
      _ ≤ ((∏ p ∈ S, (p : ℝ)) ^ δ * T ^ (-δ)) * ∏ p ∈ S, C / (p : ℝ) :=
            mul_le_mul_of_nonneg_right hge1 hg_nonneg
      _ = T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)) := by rw [hPS, key]
  have h2 : (∑ S ∈ s.powerset.filter (fun S : Finset ℕ => T < ∏ p ∈ S, (p : ℝ)),
        T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)))
      ≤ ∑ S ∈ s.powerset, T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro S hS _
    refine mul_nonneg (Real.rpow_nonneg hT.le _) (Finset.prod_nonneg (fun p hp' => ?_))
    exact mul_nonneg hC (Real.rpow_nonneg (le_of_lt (hp p (Finset.mem_powerset.mp hS hp'))) _)
  have h3 : (∑ S ∈ s.powerset, T ^ (-δ) * ∏ p ∈ S, (C * (p : ℝ) ^ (δ - 1)))
      = T ^ (-δ) * ∏ p ∈ s, (1 + C * (p : ℝ) ^ (δ - 1)) := by
    rw [← Finset.mul_sum, Finset.prod_one_add]
  linarith [h1, h2, h3]

/-- The Rankin factor `(Dpi x κ)^{-δ}`, `δ = 1/(2 (log log x)²)`, is at most
`(log x)^{-κ/2}` in the range `κ ≥ 1`, `log log x ≥ 2`. -/
private lemma Dpi_rpow_neg_le_aux (κ : ℝ) (x : ℕ) (hκ : 1 ≤ κ)
    (hL : 2 ≤ Real.log (Real.log (x : ℝ))) :
    ((Work.FIChain.Dpi x κ : ℝ)) ^ (-(1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2)))
      ≤ (Real.log (x : ℝ)) ^ (-(κ / 2)) := by
  have hlogx_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hlogx_pos : 0 < Real.log (x : ℝ) := by
    rcases eq_or_lt_of_le hlogx_nonneg with h | h
    · exfalso
      have h2 : Real.log (Real.log (x : ℝ)) = 0 := by rw [← h, Real.log_zero]
      linarith
    · exact h
  have hLpos : 0 < Real.log (Real.log (x : ℝ)) := by linarith
  have hδ0 : -(1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2)) ≤ 0 := by
    have : (0:ℝ) < 2 * (Real.log (Real.log (x : ℝ))) ^ 2 := by positivity
    have : 0 < 1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2) := by positivity
    linarith
  have hE : Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) ≤ ((Work.FIChain.Dpi x κ : ℝ)) := by
    rw [Work.FIChain.Dpi]; exact Nat.le_ceil _
  have step1 : ((Work.FIChain.Dpi x κ : ℝ)) ^ (-(1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2)))
      ≤ (Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3)) ^ (-(1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2))) :=
    Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hE hδ0
  have step2 : (Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3)) ^ (-(1 / (2 * (Real.log (Real.log (x : ℝ))) ^ 2)))
      = Real.exp (-(κ * Real.log (Real.log (x : ℝ)) / 2)) := by
    rw [← Real.exp_mul]
    congr 1
    have hLne : Real.log (Real.log (x : ℝ)) ≠ 0 := ne_of_gt hLpos
    field_simp
  have step3 : Real.exp (-(κ * Real.log (Real.log (x : ℝ)) / 2))
      = (Real.log (x : ℝ)) ^ (-(κ / 2)) := by
    rw [show -(κ * Real.log (Real.log (x:ℝ)) / 2) = Real.log (Real.log (x:ℝ)) * (-(κ/2)) by ring,
      Real.exp_mul, Real.exp_log hlogx_pos]
  linarith [step1, step2, step3]

/-- **Rankin's trick for the `Δπ`-tail of the divisibility sum.**
The `∏_{p ∈ S} 2^k / p`-weighted sum over those subsets `S` of the primes `≤ Pz` with
`∏_{p ∈ S} p > Dpi x κ` is bounded by `(log x)^{-κ/2}` times a truncated Euler product whose
local factors are the terms `1 + 2^k p^{1/(2 (log log x)²)}/p`. -/
theorem rankin_dpi_sum_le (k : ℕ) (κ : ℝ) (x Pz : ℕ) (hκ : 1 ≤ κ)
    (hL : 2 ≤ Real.log (Real.log (x : ℝ))) :
    (∑ S ∈ (Nat.primesLE Pz).powerset.filter (fun S => Work.FIChain.Dpi x κ < ∏ p ∈ S, p),
        ∏ p ∈ S, (2:ℝ)^k / (p:ℝ))
      ≤ (Real.log (x : ℝ)) ^ (-(κ / 2)) *
        ∏ p ∈ Nat.primesLE Pz,
          (1 + (2:ℝ)^k * ((p : ℝ) ^ ((1:ℝ) / (2 * (Real.log (Real.log (x:ℝ)))^2)) / (p:ℝ))) := by
  classical
  set L : ℝ := Real.log (Real.log (x:ℝ)) with hLdef
  set δ : ℝ := (1:ℝ) / (2 * L^2) with hδdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hδ_nonneg : 0 ≤ δ := by rw [hδdef]; positivity
  have hC_nonneg : (0:ℝ) ≤ (2:ℝ)^k := by positivity
  have hT_pos : (0:ℝ) < (Work.FIChain.Dpi x κ : ℝ) := by
    have hE : (0:ℝ) < Real.exp (κ * L^3) := Real.exp_pos _
    have hle : Real.exp (κ * L^3) ≤ ((Work.FIChain.Dpi x κ : ℝ)) := by
      rw [hLdef, Work.FIChain.Dpi]; exact Nat.le_ceil _
    linarith
  have hp : ∀ p ∈ Nat.primesLE Pz, (0:ℝ) < (p:ℝ) := by
    intro p hp
    have hprime : p.Prime := (Nat.mem_primesLE.mp hp).2
    exact_mod_cast hprime.pos
  have hflt : (Nat.primesLE Pz).powerset.filter (fun S => Work.FIChain.Dpi x κ < ∏ p ∈ S, p)
      = (Nat.primesLE Pz).powerset.filter
          (fun S : Finset ℕ => ((Work.FIChain.Dpi x κ : ℝ)) < ∏ p ∈ S, (p:ℝ)) := by
    apply Finset.filter_congr
    intro S _
    rw [← Nat.cast_prod, Nat.cast_lt]
  have hr := rankin_powerset_sum_le_aux (Nat.primesLE Pz) ((Work.FIChain.Dpi x κ : ℝ)) δ ((2:ℝ)^k)
      hT_pos hδ_nonneg hC_nonneg hp
  have hT_bound : ((Work.FIChain.Dpi x κ : ℝ)) ^ (-δ) ≤ (Real.log (x:ℝ))^(-(κ/2)) := by
    rw [hδdef, hLdef]; exact Dpi_rpow_neg_le_aux κ x hκ hL
  have hfac : ∀ p ∈ Nat.primesLE Pz,
      (p:ℝ)^(δ - 1) = (p:ℝ)^δ / (p:ℝ) := by
    intro p hpmem
    have hp' : (0:ℝ) < (p:ℝ) := hp p hpmem
    rw [show δ - 1 = δ + (-1) by ring, Real.rpow_add hp' δ (-1), div_eq_mul_inv,
      ← Real.rpow_neg_one (p:ℝ)]
  have hProd_eq : (∏ p ∈ Nat.primesLE Pz, (1 + (2:ℝ)^k * (p:ℝ)^(δ - 1)))
      = ∏ p ∈ Nat.primesLE Pz,
          (1 + (2:ℝ)^k * ((p : ℝ) ^ ((1:ℝ) / (2 * (Real.log (Real.log (x:ℝ)))^2)) / (p:ℝ))) := by
    apply Finset.prod_congr rfl
    intro p hpmem
    rw [hfac p hpmem]
  have hProd_nonneg : 0 ≤ ∏ p ∈ Nat.primesLE Pz, (1 + (2:ℝ)^k * (p:ℝ)^(δ - 1)) := by
    apply Finset.prod_nonneg
    intro p hpmem
    have hp' : (0:ℝ) < (p:ℝ) := hp p hpmem
    have h1 : 0 < (p:ℝ)^(δ - 1) := Real.rpow_pos_of_pos hp' _
    have h2 : (0:ℝ) ≤ (2:ℝ)^k := hC_nonneg
    nlinarith [mul_nonneg h2 (le_of_lt h1)]
  calc (∑ S ∈ (Nat.primesLE Pz).powerset.filter (fun S => Work.FIChain.Dpi x κ < ∏ p ∈ S, p),
        ∏ p ∈ S, (2:ℝ)^k / (p:ℝ))
      ≤ ((Work.FIChain.Dpi x κ : ℝ)) ^ (-δ) *
          ∏ p ∈ Nat.primesLE Pz, (1 + (2:ℝ)^k * (p:ℝ)^(δ - 1)) := by
        rw [hflt]; exact hr
    _ ≤ (Real.log (x:ℝ))^(-(κ/2)) *
          ∏ p ∈ Nat.primesLE Pz, (1 + (2:ℝ)^k * (p:ℝ)^(δ - 1)) :=
        mul_le_mul_of_nonneg_right hT_bound hProd_nonneg
    _ = (Real.log (x:ℝ))^(-(κ/2)) *
          ∏ p ∈ Nat.primesLE Pz,
            (1 + (2:ℝ)^k * ((p : ℝ) ^ ((1:ℝ) / (2 * (Real.log (Real.log (x:ℝ)))^2)) / (p:ℝ))) := by
        rw [hProd_eq]

end Work.FIChain
