import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbdDefs

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped BigOperators

/-- The `L¹`-mass of the `a'`-th derivative of the bump `φ_N` sits at scale
`fibLam₁ N k₁ ^ (1 - a')`: the elementary scale `2^{Log N}/2^{k₁}` raised to `a' - 1` is
`fibLam₁ N k₁ * ((fibLam₁ N k₁ * N)⁻¹)^a'` once the `N^{-a'}` of the `(anf)` bookkeeping
is folded in. -/
private lemma fibreMass_sumA_key (N k a' : ℕ) :
    ((N:ℝ) ^ (a' : ℤ))⁻¹ * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k)^((a':ℝ)-1)
      = fibLam₁ N k * ((fibLam₁ N k * N)⁻¹)^a' := by
  have hx : (0:ℝ) < Work.KMTPlan.A6.lothN N / 2^k :=
    div_pos (Work.KMTPlan.A6.lothN_pos N) (pow_pos (by norm_num) k)
  have hlam : fibLam₁ N k = (Work.KMTPlan.A6.lothN N / 2^k)⁻¹ := fibLam₁_eq_inv N k
  rw [hlam]
  set x := Work.KMTPlan.A6.lothN N / 2^k with hxdef
  have hx0 : 0 < x := hx
  rw [Real.rpow_sub hx0 (a':ℝ) 1, Real.rpow_one, Real.rpow_natCast, zpow_natCast]
  rw [← inv_pow, mul_inv, inv_inv, mul_pow]
  ring

/-- The `a'`-sum of the `(anf)` bookkeeping: with `λ₁ = fibLam₁ N k₁`, the weighted mass
`∑_{a' ≤ i₁} C(i₁,a') N^{-a'} ∫‖∂^{a'}φ_N‖` is at most `fibBumpCφ P · λ₁ · (1 + 1/(λ₁N))^{i₁}`.
This is the `fibreMass` estimate of `Work.KMTAreas.A7.FibreMassHbd`, in the form needed for the
`vu` (derivative) bookkeeping of the fibre bound. -/
theorem fibreMass_sumA (P : Polynomial ℤ) (N k₁ : ℕ) (i₁ : ℕ) (hi₁ : i₁ ≤ 2) :
    (∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹
        * (∫ ξ : ℝ, ‖iteratedDeriv a' (varphiN N k₁) ξ‖))
      ≤ fibBumpCφ P * fibLam₁ N k₁ * (1 + 1 / (fibLam₁ N k₁ * (N : ℝ))) ^ i₁ := by
  have hstep1 : (∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹
        * (∫ ξ : ℝ, ‖iteratedDeriv a' (varphiN N k₁) ξ‖))
      ≤ ∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹
        * (fibBumpCφ P * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℝ)-1)) := by
    refine Finset.sum_le_sum (fun a' ha' => ?_)
    have ha'2 : a' ≤ 2 := by
      have hlt : a' < i₁ + 1 := Finset.mem_range.mp ha'
      omega
    have hI : (∫ ξ : ℝ, ‖iteratedDeriv a' (varphiN N k₁) ξ‖)
        ≤ fibBumpCφ P * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℝ)-1) :=
      fibBumpCφ_bound P N k₁ a' ha'2
    refine mul_le_mul_of_nonneg_left hI ?_
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (zpow_nonneg (Nat.cast_nonneg N) _))
  refine le_trans hstep1 ?_
  have hB : (∑ a' ∈ Finset.range (i₁ + 1),
        (i₁.choose a' : ℝ) * ((N:ℝ)^(a':ℤ))⁻¹
          * (fibBumpCφ P * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℝ)-1)))
      = ∑ a' ∈ Finset.range (i₁ + 1),
          (i₁.choose a' : ℝ) * fibBumpCφ P * fibLam₁ N k₁
            * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a' := by
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    calc (i₁.choose a' : ℝ) * ((N:ℝ)^(a':ℤ))⁻¹
          * (fibBumpCφ P * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℝ)-1))
        = (i₁.choose a' : ℝ) * fibBumpCφ P
            * (((N:ℝ)^(a':ℤ))⁻¹ * (Work.KMTPlan.A6.lothN N / (2:ℝ)^k₁)^((a':ℝ)-1)) := by ring
      _ = (i₁.choose a' : ℝ) * fibBumpCφ P
            * (fibLam₁ N k₁ * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a') := by rw [fibreMass_sumA_key]
      _ = (i₁.choose a' : ℝ) * fibBumpCφ P * fibLam₁ N k₁
            * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a' := by ring
  have hbin : (∑ a' ∈ Finset.range (i₁ + 1),
        (i₁.choose a' : ℝ) * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a')
      = (1 + (fibLam₁ N k₁ * (N:ℝ))⁻¹)^i₁ := by
    have h1 : (∑ a' ∈ Finset.range (i₁ + 1),
          (i₁.choose a' : ℝ) * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a')
        = ∑ a' ∈ Finset.range (i₁ + 1),
            ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a' * (1:ℝ)^(i₁ - a') * (i₁.choose a' : ℝ) := by
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [one_pow, mul_one]; ring
    rw [h1, ← add_pow, add_comm]
  have hC : (∑ a' ∈ Finset.range (i₁ + 1),
        (i₁.choose a' : ℝ) * fibBumpCφ P * fibLam₁ N k₁
          * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a')
      = fibBumpCφ P * fibLam₁ N k₁ * (1 + 1 / (fibLam₁ N k₁ * (N:ℝ)))^i₁ := by
    rw [show (∑ a' ∈ Finset.range (i₁ + 1),
          (i₁.choose a' : ℝ) * fibBumpCφ P * fibLam₁ N k₁
            * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a')
        = (fibBumpCφ P * fibLam₁ N k₁)
          * ∑ a' ∈ Finset.range (i₁ + 1),
              (i₁.choose a' : ℝ) * ((fibLam₁ N k₁ * (N:ℝ))⁻¹)^a' from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a' _ => by ring)]
    rw [hbin, one_div]
  rw [hB, hC]

end Work.KMTAreas.A7
