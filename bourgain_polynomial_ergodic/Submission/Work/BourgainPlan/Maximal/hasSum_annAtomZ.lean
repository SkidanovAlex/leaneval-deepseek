import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusPartitionDefs

/-!
# The dyadic annulus partition of unity sums to one

This file proves `∑'_m annAtomZ m ξ = 1` for `ξ ≠ 0`, i.e. that the smooth dyadic
annulus atoms of `annulusPartitionDefs` form a partition of unity away from the origin.

The proof is the classical dyadic telescoping.  Since `annAtom x = annStep (2x) - annStep x`,
the partial sums over `m = 0, …, N-1` collapse to `annStep (2^N ξ) - annStep ξ`, which is
eventually `1 - annStep ξ` because `2^N |ξ| → ∞` and `annStep = 1` outside `(-3/2, 3/2)`;
symmetrically the partial sums over `m = 0, -1, …, -(N-1)` collapse to
`annStep (2ξ) - annStep (2ξ / 2^N)`, which is eventually `annStep (2ξ)` because
`annStep = 0` on `[-1,1]`.  The two one-sided `HasSum`s are glued by `HasSum.of_nat_of_neg`.
-/

open scoped BigOperators
open Filter

namespace Work.BourgainPlan.Maximal

/-- Telescoping step for nonnegative indices, in `ℕ`-power form:
`annAtomZ n ξ = annStep (2^{n+1} ξ) - annStep (2^n ξ)`. -/
lemma annAtomZ_nat_eq (n : ℕ) (ξ : ℝ) :
    annAtomZ (n : ℤ) ξ = annStep ((2 : ℝ) ^ (n + 1) * ξ) - annStep ((2 : ℝ) ^ n * ξ) := by
  have h1 : (2 : ℝ) * ((2 : ℝ) ^ (n : ℤ) * ξ) = ((2 : ℝ) ^ (n + 1)) * ξ := by
    rw [zpow_natCast, pow_succ]; ring
  have h2 : ((2 : ℝ) ^ (n : ℤ)) * ξ = ((2 : ℝ) ^ n) * ξ := by rw [zpow_natCast]
  unfold annAtomZ annAtom
  rw [h1, h2]

/-- Telescoping step for nonpositive indices, in `ℕ`-power form:
`annAtomZ (-n) ξ = annStep (2ξ / 2^n) - annStep (2ξ / 2^{n+1})`. -/
lemma annAtomZ_neg_nat_eq (n : ℕ) (ξ : ℝ) :
    annAtomZ (-(n : ℤ)) ξ
      = annStep (2 * ξ / (2 : ℝ) ^ n) - annStep (2 * ξ / (2 : ℝ) ^ (n + 1)) := by
  have hpow : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hA : (2 : ℝ) ^ (-(n : ℤ)) * ξ = 2 * ξ / (2 : ℝ) ^ (n + 1) := by
    rw [hpow, div_eq_mul_inv, pow_succ]; field_simp
  have hB : (2 : ℝ) * ((2 : ℝ) ^ (-(n : ℤ)) * ξ) = 2 * ξ / (2 : ℝ) ^ n := by
    rw [hA]; ring
  unfold annAtomZ annAtom
  rw [hB, hA]

/-- The partial sums of the atoms over `m = 0, …, N-1` telescope:
`∑_{n<N} annAtomZ n ξ = annStep (2^N ξ) - annStep ξ`. -/
lemma sum_range_annAtomZ (N : ℕ) (ξ : ℝ) :
    ∑ n ∈ Finset.range N, annAtomZ (n : ℤ) ξ
      = annStep ((2 : ℝ) ^ N * ξ) - annStep ξ := by
  have key : ∑ i ∈ Finset.range N,
      (annStep ((2 : ℝ) ^ (i + 1) * ξ) - annStep ((2 : ℝ) ^ i * ξ))
      = annStep ((2 : ℝ) ^ N * ξ) - annStep ξ := by
    simpa using Finset.sum_range_sub (fun i : ℕ => annStep ((2 : ℝ) ^ i * ξ)) N
  rw [← key]
  exact Finset.sum_congr rfl (fun i _ => (annAtomZ_nat_eq i ξ))

/-- The partial sums of the atoms over `m = 0, -1, …, -(N-1)` telescope:
`∑_{n<N} annAtomZ (-n) ξ = annStep (2ξ) - annStep (2ξ / 2^N)`. -/
lemma sum_range_annAtomZ_neg (N : ℕ) (ξ : ℝ) :
    ∑ n ∈ Finset.range N, annAtomZ (-(n : ℤ)) ξ
      = annStep (2 * ξ) - annStep (2 * ξ / (2 : ℝ) ^ N) := by
  have key : ∑ i ∈ Finset.range N,
      (annStep (2 * ξ / (2 : ℝ) ^ i) - annStep (2 * ξ / (2 : ℝ) ^ (i + 1)))
      = annStep (2 * ξ) - annStep (2 * ξ / (2 : ℝ) ^ N) := by
    simpa using Finset.sum_range_sub' (fun i : ℕ => annStep (2 * ξ / (2 : ℝ) ^ i)) N
  rw [← key]
  exact Finset.sum_congr rfl (fun i _ => (annAtomZ_neg_nat_eq i ξ))

/-- The atoms at nonnegative indices sum to `1 - annStep ξ` when `ξ ≠ 0`: the partial sums
reach `annStep (2^N ξ) - annStep ξ`, and `annStep (2^N ξ) = 1` for `N` large. -/
lemma hasSum_annAtomZ_nat (ξ : ℝ) (hξ : ξ ≠ 0) :
    HasSum (fun n : ℕ => annAtomZ (n : ℤ) ξ) (1 - annStep ξ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => annAtomZ_nonneg _ _)]
  have hξpos : 0 < |ξ| := abs_pos.mpr hξ
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (3 / 2 / |ξ|) (show (1 : ℝ) < 2 by norm_num)
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, annAtomZ (n : ℤ) ξ) = 1 - annStep ξ := by
    refine Filter.eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
    rw [sum_range_annAtomZ]
    have hle : (2 : ℝ) ^ N₀ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    have hgt : 3 / 2 ≤ (2 : ℝ) ^ N * |ξ| := by
      have h1 : 3 / 2 / |ξ| < (2 : ℝ) ^ N₀ := hN₀
      rw [div_lt_iff₀ hξpos] at h1
      nlinarith
    have hstep : annStep ((2 : ℝ) ^ N * ξ) = 1 := by
      apply annStep_eq_one_of_three_halves_le
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N)]
      exact hgt
    rw [hstep]
  exact Tendsto.congr' (hev.mono fun N hN => hN.symm) tendsto_const_nhds

/-- The atoms at nonpositive indices sum to `annStep (2ξ)`: the partial sums reach
`annStep (2ξ) - annStep (2ξ / 2^N)`, and `annStep (2ξ / 2^N) = 0` for `N` large. -/
lemma hasSum_annAtomZ_neg (ξ : ℝ) :
    HasSum (fun n : ℕ => annAtomZ (-(n : ℤ)) ξ) (annStep (2 * ξ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => annAtomZ_nonneg _ _)]
  obtain ⟨N₁, hN₁⟩ := pow_unbounded_of_one_lt (2 * |ξ|) (show (1 : ℝ) < 2 by norm_num)
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, annAtomZ (-(n : ℤ)) ξ) = annStep (2 * ξ) := by
    refine Filter.eventually_atTop.2 ⟨N₁, fun N hN => ?_⟩
    rw [sum_range_annAtomZ_neg]
    have hle : (2 : ℝ) ^ N₁ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
    have hlt : 2 * |ξ| < (2 : ℝ) ^ N := lt_of_lt_of_le hN₁ hle
    have hstep : annStep (2 * ξ / (2 : ℝ) ^ N) = 0 := by
      apply annStep_eq_zero_of_abs_le_one
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
      rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
      exact le_of_lt hlt
    rw [hstep, sub_zero]
  exact Tendsto.congr' (hev.mono fun N hN => hN.symm) tendsto_const_nhds

/-- **The dyadic annulus partition telescopes.**  For every `ξ ≠ 0` the atoms
`Work.BourgainPlan.Maximal.annAtomZ m ξ` sum to one over `m ∈ ℤ` (equivalently
`∑'_m annAtomZ m ξ = 1`).  This is the partition-of-unity identity underlying the
Littlewood--Paley decomposition built from `Work.BourgainPlan.Maximal.annAtomC`.

Route.  The dyadic telescoping gives, for `K ≤ M`,
`∑_{m=K}^{M-1} annAtom (2^m ξ) = annStep (2^M ξ) - annStep (2^K ξ)`
(since `annAtom y = annStep (2y) - annStep y`); as `M → ∞` the first term tends to `1` (because
`Work.BourgainPlan.Maximal.annStep = 1` outside `(-3/2,3/2)` and `2^M |ξ| → ∞`) and as `K → -∞` the
second tends to `0` (because `annStep = 0` on `[-1,1]`).  Concretely, prove
`HasSum (fun n : ℕ => annAtomZ (n : ℤ) ξ) (1 - annStep ξ)` and
`HasSum (fun n : ℕ => annAtomZ (-(n : ℤ)) ξ) (annStep (2 * ξ))` by
`hasSum_iff_tendsto_nat_of_nonneg` plus `Finset.sum_range_sub`/`Finset.sum_range_sub'` (the partial
sums are eventually constant by `annStep_eq_zero_of_abs_le_one` and
`annStep_eq_one_of_three_halves_le`), then combine with `HasSum.of_nat_of_neg` (noting
`f 0 = annStep (2 * ξ) - annStep ξ`). -/
theorem hasSum_annAtomZ (ξ : ℝ) (hξ : ξ ≠ 0) :
    HasSum (fun m : ℤ => Work.BourgainPlan.Maximal.annAtomZ m ξ) 1 := by
  have h1 := hasSum_annAtomZ_nat ξ hξ
  have h2 := hasSum_annAtomZ_neg ξ
  have h := HasSum.of_nat_of_neg (f := fun m : ℤ => Work.BourgainPlan.Maximal.annAtomZ m ξ) h1 h2
  have hval : Work.BourgainPlan.Maximal.annAtomZ (0 : ℤ) ξ = annStep (2 * ξ) - annStep ξ := by
    simp [annAtomZ, annAtom]
  rw [hval] at h
  rw [show (1 - annStep ξ) + annStep (2 * ξ) - (annStep (2 * ξ) - annStep ξ) = 1 from by
        ring] at h
  exact h

end Work.BourgainPlan.Maximal
