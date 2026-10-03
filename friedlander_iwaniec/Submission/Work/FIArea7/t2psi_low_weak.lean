import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.t2psiLowStep
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Work.FIArea7.t2psiLowSumMin

namespace Work.FIArea7

open Finset
open scoped BigOperators

-- The proof is the same as `Work.FIArea7.t2psi_low` (which is proved in
-- `Submission/Work/FIArea7/t2psi_low.lean`); only the two range hypotheses on `Y` are dropped.
-- Useful imports: `Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit`,
-- `Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube`,
-- `Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`.

/-- **Finset plumbing.**  If the summand `f` vanishes above `N`, then the sum over `a ∈ Icc 1 Y`
may be shrunk to `a ∈ Icc 1 (min Y N)`. -/
lemma t2psi_low_weak_shrink_sum {M : Type*} [AddCommMonoid M] {f : ℕ → M} {N Y : ℕ}
    (h : ∀ a : ℕ, N < a → f a = 0) :
    ∑ a ∈ Finset.Icc 1 Y, f a = ∑ a ∈ Finset.Icc 1 (min Y N), f a := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    exact ⟨ha.1, le_trans ha.2 (min_le_left _ _)⟩
  · intro a haY hnot
    rw [Finset.mem_Icc] at haY
    have hgt : N < a := by
      by_contra hc
      rw [not_lt] at hc
      exact hnot (by rw [Finset.mem_Icc]; exact ⟨haY.1, le_min haY.2 hc⟩)
    exact h a hgt

/-- **The low (`a ≤ Y`) part of the Möbius-log split, weak form** — the same estimate as
`Work.FIArea7.t2psi_low` but without any hypothesis on `Y` beyond `1 ≤ Y`. -/
theorem t2psi_low_weak (h32 : Work.FIArea7.Prop232) :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧
      ∀ (N c d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (Y : ℕ),
        1 ≤ N → 1 ≤ c → 1 ≤ d → 1 ≤ Y →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a b' : ℤ), chi (⟨a + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a, b'⟩) →
        (∀ (a b' : ℤ), chi (⟨a, b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a, b'⟩) →
        ‖∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / a),
              ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (a * m))‖
          ≤ K * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3:ℝ)/4) * (Y : ℝ) ^ ((3:ℝ)/4)
              * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ B := by
  obtain ⟨C1, hC1pos, hstep⟩ := Work.FIArea7.t2psiLowStep h32
  obtain ⟨K1, hK1pos, hsum⟩ := Work.FIArea7.t2psiLowSumMin
  refine ⟨C1 * K1, 18, by positivity, by norm_num, ?_⟩
  intro N c d k chi Y hN hc hd hY hchi hmul hp1 hp2
  have hmu : ∀ a : ℕ, ‖(ArithmeticFunction.moebius a : ℂ)‖ ≤ 1 := by
    intro a
    rw [Complex.norm_intCast]
    have h : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    exact h
  have hshrink : (∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / a),
          ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
            (c * (a * m)))
      = ∑ a ∈ Finset.Icc 1 (min Y N), (ArithmeticFunction.moebius a : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / a),
          ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
            (c * (a * m)) := by
    apply t2psi_low_weak_shrink_sum
    intro a ha
    rw [Nat.div_eq_of_lt ha]
    simp
  have hpoint : ∀ a ∈ Finset.Icc 1 (min Y N),
      ‖∑ m ∈ Finset.Icc 1 (N / a),
          ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
            (c * (a * m))‖
        ≤ C1 * (d : ℝ) * (|(k : ℝ)| + 1) * (((c * a).divisors.card : ℕ) : ℝ) ^ 4
            * Real.sqrt (((c * a : ℕ) : ℝ)) * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
            * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 2 := by
    intro a ha
    have h := hstep N c d a k chi hN hc hd (Finset.mem_Icc.mp ha).1 hchi hmul hp1 hp2
    have hca : ((c : ℝ) * (a : ℝ)) = ((c * a : ℕ) : ℝ) := (Nat.cast_mul c a).symm
    rwa [hca] at h
  rw [hshrink]
  calc ‖∑ a ∈ Finset.Icc 1 (min Y N), (ArithmeticFunction.moebius a : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / a),
          ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
            (c * (a * m))‖
      ≤ ∑ a ∈ Finset.Icc 1 (min Y N), ‖(ArithmeticFunction.moebius a : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / a),
          ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
            (c * (a * m))‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 (min Y N),
          ‖∑ m ∈ Finset.Icc 1 (N / a),
            ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k)
              (c * (a * m))‖ := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hmu a)
    _ ≤ ∑ a ∈ Finset.Icc 1 (min Y N), C1 * (d : ℝ) * (|(k : ℝ)| + 1)
          * (((c * a).divisors.card : ℕ) : ℝ) ^ 4 * Real.sqrt (((c * a : ℕ) : ℝ))
          * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4))
          * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 2 := Finset.sum_le_sum hpoint
    _ = (C1 * (d : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 2)
          * ∑ a ∈ Finset.Icc 1 (min Y N), (((c * a).divisors.card : ℕ) : ℝ) ^ 4
              * Real.sqrt (((c * a : ℕ) : ℝ)) * (((N : ℝ) / (a : ℝ)) ^ ((3 : ℝ) / 4)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a ha => ?_
        ring
    _ ≤ (C1 * (d : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 2)
          * (K1 * (c : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) * (Y : ℝ) ^ ((3 : ℝ) / 4)
              * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ 16) :=
        mul_le_mul_of_nonneg_left (hsum N c Y hN hc hY) (by positivity)
    _ = (C1 * K1) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((3 : ℝ) / 4)
          * (Y : ℝ) ^ ((3 : ℝ) / 4) * (Real.log ((c : ℝ) * (N : ℝ) + 2)) ^ (18 : ℝ) := by
        rw [Real.rpow_ofNat]
        ring

end Work.FIArea7
