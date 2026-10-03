/-
# `FIArea2/R6/Swapper6.lean` — exchanging the `u`-sum with the `h`-tsum in the §9 pair weight

`Count.sec9_Lsum_avg_final_of_box4` produces the §9 lacunarity bound with the finite `(u₁,u₂)`-sum
*outside* and the `h`-tsum inside; the hypothesis `hL` of `R6/sec9Psum_le_of_Lsum_six` (and hence
`Inputs6.LacProp`) has the `h`-tsum outside.  The two agree because `τ₄` has average order
polylog: `summable_Wt_tau4_gen` (the `H`-uniform version of `Count.summable_Wt_tau4`) supplies the
summability needed for `Summable.tsum_finsetSum`.
-/
import Mathlib
import Submission.Work.FIArea2.Count.summable_Wt_tau4

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §9 weight `(1+h₁²/H²)^{-1}(1+h₂²/H²)^{-1}τ₄(u₁h₁²−u₂h₂²)` is summable in `h`, for every
`H ≥ 1` and every `(u₁,u₂)` (the proof is that of `Count.summable_Wt_tau4`, with `H` in place of
`Hscale M N`). -/
theorem summable_Wt_tau4_gen (H : ℝ) (hH : 1 ≤ H) (u1 u2 : ℤ) :
    Summable (fun h : ℤ × ℤ =>
      (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ((1:ℝ)/16) (by norm_num)
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH
  let K : ℝ := (1 + H ^ 2) ^ 2
  have hH2 : (0 : ℝ) < 1 + H ^ 2 := by positivity
  have hKpos : 0 < K := by
    have := pow_pos hH2 2
    exact this
  have hb : Summable (fun t : ℤ => (1 + (t:ℝ)^2)⁻¹) :=
    (Work.FIArea2.summable_Wt 1 le_rfl).congr (fun t => by simp [Work.FIArea2.Wt])
  have hw : Summable (fun t : ℤ => |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹) :=
    Work.FIArea2.Count.summable_abs_sqrt_mul_one_add_sq_inv
  have hbnn : ∀ t : ℤ, 0 ≤ (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwnn : ∀ t : ℤ, 0 ≤ |(t:ℝ)|^((1:ℝ)/2) * (1 + (t:ℝ)^2)⁻¹ := fun t => by positivity
  have hwb : Summable (fun p : ℤ × ℤ =>
      |(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹) :=
    Summable.mul_of_nonneg hw hb hwnn hbnn
  have hbw : Summable (fun p : ℤ × ℤ =>
      (1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) :=
    Summable.mul_of_nonneg hb hw hbnn hwnn
  let G : ℤ × ℤ → ℝ := fun p => K * Cd^4 *
      ( |(u1:ℝ)|^((1:ℝ)/4) * (|(p.1:ℝ)|^((1:ℝ)/2) * (1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹)
      + |(u2:ℝ)|^((1:ℝ)/4) * ((1 + (p.1:ℝ)^2)⁻¹ * (|(p.2:ℝ)|^((1:ℝ)/2) * (1 + (p.2:ℝ)^2)⁻¹)) )
  have hG : Summable G :=
    ((hwb.mul_left (|(u1:ℝ)|^((1:ℝ)/4))).add (hbw.mul_left (|(u2:ℝ)|^((1:ℝ)/4)))).mul_left (K * Cd^4)
  refine Summable.of_nonneg_of_le (f := G) ?_ ?_ hG
  · intro p
    exact mul_nonneg (by positivity) (by positivity)
  · intro p
    have e1 := Work.FIArea2.Count.inv_one_add_div_sq_le H (p.1 : ℝ) hHpos
    have e2 := Work.FIArea2.Count.inv_one_add_div_sq_le H (p.2 : ℝ) hHpos
    have hA : (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        ≤ K * ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) := by
      refine (mul_le_mul e1 e2 (by positivity) (by positivity)).trans (le_of_eq ?_)
      simp only [K]; ring
    have hB := Work.FIArea2.Count.tau4_le Cd hCdpos hCd u1 u2 p.1 p.2
    have hAnn : 0 ≤ K * ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) := by positivity
    have hBnn : 0 ≤ ((((u1 * p.1^2 - u2*p.2^2).natAbs.divisors.card : ℝ))^4) := by positivity
    calc (1 + (p.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2 / H ^ 2)⁻¹
            * ((((u1 * p.1^2 - u2*p.2^2).natAbs.divisors.card : ℝ))^4)
        ≤ (K * ((1 + (p.1:ℝ)^2)⁻¹ * (1 + (p.2:ℝ)^2)⁻¹))
          * (Cd^4 * ( |(u1:ℝ)|^((1:ℝ)/4) * |(p.1:ℝ)|^((1:ℝ)/2)
                    + |(u2:ℝ)|^((1:ℝ)/4) * |(p.2:ℝ)|^((1:ℝ)/2) )) :=
          mul_le_mul hA hB hBnn hAnn
      _ = G p := by
          simp only [G]
          ring

/-- **The `u`-sum / `h`-tsum exchange** of the §9 pair weight. -/
theorem swap_uh (H : ℝ) (hH : 1 ≤ H) (R : ℕ) :
    (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
        (Nat.gcd u1.natAbs u2.natAbs : ℝ)
          * (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
              * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
      = (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
          * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              (Nat.gcd u1.natAbs u2.natAbs : ℝ)
                * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4))) := by
  set A : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ) with hA
  set W : ℤ × ℤ → ℝ := fun h => (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
    with hW
  set T : ℤ × ℤ → ℤ × ℤ → ℝ :=
    fun p h => (((p.1 * h.1 ^ 2 - p.2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4) with hT
  set f : (ℤ × ℤ) → (ℤ × ℤ) → ℝ :=
    fun p h => (Nat.gcd p.1.natAbs p.2.natAbs : ℝ) * (W h * T p h) with hf
  have hsumm : ∀ p ∈ A ×ˢ A, Summable (f p) := by
    intro p _
    have hEq : f p = fun h : ℤ × ℤ =>
        (Nat.gcd p.1.natAbs p.2.natAbs : ℝ)
          * ((1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
              * (((p.1 * h.1 ^ 2 - p.2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := by
      funext h; rw [hf, hW, hT]
    rw [hEq]
    exact (summable_Wt_tau4_gen H hH p.1 p.2).mul_left _
  have key : (∑' h : ℤ × ℤ, ∑ p ∈ A ×ˢ A, f p h) = ∑ p ∈ A ×ˢ A, ∑' h : ℤ × ℤ, f p h :=
    Summable.tsum_finsetSum (L := SummationFilter.unconditional (ℤ × ℤ))
      (f := f) (s := A ×ˢ A) hsumm
  have hL : (∑ u1 ∈ A, ∑ u2 ∈ A, (Nat.gcd u1.natAbs u2.natAbs : ℝ)
        * (∑' h : ℤ × ℤ, W h * T (u1, u2) h))
      = ∑ p ∈ A ×ˢ A, ∑' h : ℤ × ℤ, f p h := by
    rw [← Finset.sum_product A A (fun p : ℤ × ℤ =>
      (Nat.gcd p.1.natAbs p.2.natAbs : ℝ) * (∑' h : ℤ × ℤ, W h * T p h))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← tsum_mul_left]
  have hR : (∑' h : ℤ × ℤ, W h * (∑ u1 ∈ A, ∑ u2 ∈ A,
        (Nat.gcd u1.natAbs u2.natAbs : ℝ) * T (u1, u2) h))
      = ∑' h : ℤ × ℤ, ∑ p ∈ A ×ˢ A, f p h := by
    refine tsum_congr fun h => ?_
    rw [← Finset.sum_product A A (fun p : ℤ × ℤ =>
      (Nat.gcd p.1.natAbs p.2.natAbs : ℝ) * T p h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hf]; ring
  rw [hL, hR, key]

end

end Work.FIArea2.R6
