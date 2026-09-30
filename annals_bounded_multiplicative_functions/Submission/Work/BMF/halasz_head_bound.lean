import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_lipschitz
import Submission.Work.BMF.norm_cpow_neg_I_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "head bound" of the Halász argument (`Work.BMF.halasz_head_bound`)

Write `R p = Re (f p · p^{-iτ})`.  For a prime `p` and `α ≥ 0`,

`p^{-(1+α)} · R p ≤ R p / p + (1 - p^{-α}) / p`,

because `p^{-(1+α)} = p^{-α} · p^{-1}` and, after multiplying by `p`,
`(1 - p^{-α}) (R p + 1) ≥ 0` (both factors are nonnegative: `p^{-α} ≤ 1` and
`|R p| ≤ ‖f p‖ ≤ 1`).

Summing over the primes `p ≤ y` and using `mHal f y T ≤ mHalSum f y τ` (valid since `|τ| ≤ T`)
together with `Σ_{p ≤ y} R p / p = Zrcp y - mHalSum f y τ` gives the claim.
-/

open Finset Real Complex

namespace Work.BMF

/-- Termwise inequality behind `halasz_head_bound`: for a prime `p`, `α ≥ 0` and a complex
number `z` of modulus at most one,
`p^{-(1+α)} · Re z ≤ Re z / p + (1 - p^{-α}) / p`. -/
lemma rpow_head_term_bound (p : ℕ) (hp : 1 ≤ p) {α : ℝ} (hα : 0 ≤ α) (z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    (p : ℝ) ^ (-(1 + α)) * z.re ≤ z.re / p + (1 - (p : ℝ) ^ (-α)) / p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq_le : (p : ℝ) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  have habs : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have hz2 : -1 ≤ z.re := (abs_le.mp habs).1
  have hpr : (p : ℝ) ^ (-(1 + α)) = (p : ℝ) ^ (-α) * (p : ℝ)⁻¹ := by
    rw [show (-(1 + α)) = (-α) + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one]
  have hL : (p : ℝ) ^ (-(1 + α)) * z.re = ((p : ℝ) ^ (-α) * z.re) / p := by
    rw [hpr, div_eq_mul_inv]; ring
  have hR : z.re / p + (1 - (p : ℝ) ^ (-α)) / p = (z.re + (1 - (p : ℝ) ^ (-α))) / p := by
    ring
  rw [hL, hR, div_le_div_iff_of_pos_right hp0]
  have hkey : 0 ≤ (1 - (p : ℝ) ^ (-α)) * (z.re + 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hkey]

theorem halasz_head_bound (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {y α T τ : ℝ}
    (hα : 0 ≤ α) (hτ : |τ| ≤ T) :
    (∑ p ∈ (⌊y⌋₊).primesLE, (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re)
      ≤ Work.BMF.Zrcp y - Work.BMF.mHal f y T
        + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by
  -- Modulus bound for the twisted values.
  have hbnd : ∀ p : ℕ, p.Prime → ‖f p * (p : ℂ) ^ (-(Complex.I * τ))‖ ≤ 1 := by
    intro p hp
    rw [Complex.norm_mul, norm_cpow_neg_I_mul τ hp.one_le, mul_one]
    exact hb p
  -- Termwise comparison.
  have hterm : ∀ p ∈ (⌊y⌋₊).primesLE,
      (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re
        ≤ (f p * (p : ℂ) ^ (-(Complex.I * τ))).re / p + (1 - (p : ℝ) ^ (-α)) / p := by
    intro p hp
    exact rpow_head_term_bound p (Nat.prime_of_mem_primesLE hp).one_le hα _
      (hbnd p (Nat.prime_of_mem_primesLE hp))
  have hsum : (∑ p ∈ (⌊y⌋₊).primesLE,
        (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re)
      ≤ (∑ p ∈ (⌊y⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * τ))).re / p)
        + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  -- Identify `Σ R p / p` with `Zrcp y - mHalSum f y τ`.
  have hB : (∑ p ∈ (⌊y⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * τ))).re / p)
      = Zrcp y - mHalSum f y τ := by
    unfold Zrcp mHalSum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by
      have := (Nat.prime_of_mem_primesLE hp).pos
      positivity
    field_simp
    ring
  -- `mHal` is attained (as an infimum) at `τ`.
  have hle : mHal f y T ≤ mHalSum f y τ := by
    have hbdd : BddBelow (Set.range (fun u : {u : ℝ // |u| ≤ T} => mHalSum f y u.1)) :=
      ⟨0, by rintro _ ⟨u, rfl⟩; exact mHalSum_nonneg hb y u.1⟩
    exact ciInf_le hbdd ⟨τ, hτ⟩
  calc (∑ p ∈ (⌊y⌋₊).primesLE,
          (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re)
      ≤ (∑ p ∈ (⌊y⌋₊).primesLE, (f p * (p : ℂ) ^ (-(Complex.I * τ))).re / p)
          + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := hsum
    _ = (Zrcp y - mHalSum f y τ)
          + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by rw [hB]
    _ ≤ (Zrcp y - mHal f y T)
          + ∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p := by linarith

end Work.BMF
