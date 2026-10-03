import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.R6.uboxSum_le_dsum
import Submission.Work.FIArea2.R6.tau4_le_sum_cuberoot

/-!
# `FIArea2/R6/uboxSum_le_dsum3` — the box reduction at the CUBE cutoff `d³ ≤ |N|`

This is `R6/uboxSum_le_dsum` with Landreau's small-divisor cutoff `d² ≤ |N|` replaced by
`d³ ≤ |N|` (via `R6/tau4_le_sum_cuberoot`).  The changes are the exponent of `τ(d)` (`8 → 20`)
and the restriction of the outer sum to the moduli `d` that can actually occur, `d³ ≤ r(X²+Y²)`.

Keeping that restriction is what makes the reduction useful: every modulus `c ∣ d` that can occur
then satisfies `c³ ≤ d³ ≤ r(X²+Y²)`, which is exactly the hypothesis of the per-modulus estimate
`R6/WC_cube`.  With it the "hard region" `c > max(2r, X, Y)` of the per-modulus count disappears
(see `R6/WC_PERMOD_LEAD.md`, Part VII).

Downstream (`R6/ubox_bound3`) the extra `τ`-power raises the log exponent from `800` to `2^26`,
which is absorbed by raising the lacunarity cap of §9 from `2^10` to `2^27` (see `R6/BFun29`).
-/

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `k = 3` majorant in indicator form, on the cube-restricted range. -/
lemma tau4_le_sum_indicators_cube {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    ((m.divisors.card : ℝ)) ^ 4
      ≤ (2 : ℝ) ^ (20 : ℕ) *
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            (if d ∣ m then ((d.divisors.card : ℝ)) ^ 20 else (0 : ℝ)) := by
  have h1 := tau4_le_sum_cuberoot m hm
  have hsub : (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d ^ 3 ≤ m)
      ⊆ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M ∧ d ∣ m) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, hdvd, hdd⟩ := hd
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hd1, Nat.le_sqrt'.mpr ?_⟩, le_trans hdd hmM, hdvd⟩
    have hsq : d ^ 2 ≤ d ^ 3 := by
      calc d ^ 2 = d ^ 2 * 1 := (mul_one _).symm
        _ ≤ d ^ 2 * d := Nat.mul_le_mul_left _ hd1
        _ = d ^ 3 := by ring
    calc d ^ 2 ≤ d ^ 3 := hsq
      _ ≤ m := hdd
      _ ≤ M := hmM
  calc ((m.divisors.card : ℝ)) ^ 4
      ≤ (2 : ℝ) ^ (20 : ℕ) *
          ∑ d ∈ (Finset.Icc 1 m).filter (fun d => d ∣ m ∧ d ^ 3 ≤ m),
            ((d.divisors.card : ℝ)) ^ 20 := h1
    _ ≤ (2 : ℝ) ^ (20 : ℕ) *
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M ∧ d ∣ m),
            ((d.divisors.card : ℝ)) ^ 20 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
    _ = (2 : ℝ) ^ (20 : ℕ) *
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            (if d ∣ m then ((d.divisors.card : ℝ)) ^ 20 else (0 : ℝ)) := by
        congr 1
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd3 : d ^ 3 ≤ M <;> by_cases hdm : d ∣ m <;> simp [hd3, hdm]

/-- **The box reduction at the cube cutoff.** -/
theorem uboxSum_le_dsum3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (r X Y : ℕ), 1 ≤ r → 1 ≤ X → 1 ≤ Y →
      Work.FIArea2.R6.uboxSum r X Y
        ≤ C * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt (r * (X ^ 2 + Y ^ 2)))).filter
              (fun d => d ^ 3 ≤ r * (X ^ 2 + Y ^ 2)),
            ((d.divisors.card : ℝ)) ^ 20 * Work.FIArea2.R6.ndCount d r X Y := by
  refine ⟨(2 : ℝ) ^ (20 : ℕ), by positivity, ?_⟩
  intro r X Y hr hX hY
  set M : ℕ := r * (X ^ 2 + Y ^ 2) with hM
  have key : ∀ x ∈ zPz r, ∀ y ∈ zPz r, ∀ h1 ∈ zPz X, ∀ h2 ∈ zPz Y,
      T4 x y h1 h2
        ≤ ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) := by
    intro x hx y hy h1 hh1 h2 hh2
    have hxr : x.natAbs ≤ r := natAbs_le_of_mem_zPz hx
    have hyr : y.natAbs ≤ r := natAbs_le_of_mem_zPz hy
    have hh1X : h1.natAbs ≤ X := natAbs_le_of_mem_zPz hh1
    have hh2Y : h2.natAbs ≤ Y := natAbs_le_of_mem_zPz hh2
    have hmM : (x * h1 ^ 2 - y * h2 ^ 2).natAbs ≤ M := by
      have hx1 : (x * h1 ^ 2).natAbs ≤ r * X ^ 2 := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul hxr (Nat.pow_le_pow_left hh1X 2)
      have hy1 : (y * h2 ^ 2).natAbs ≤ r * Y ^ 2 := by
        rw [Int.natAbs_mul, Int.natAbs_pow]
        exact Nat.mul_le_mul hyr (Nat.pow_le_pow_left hh2Y 2)
      calc (x * h1 ^ 2 - y * h2 ^ 2).natAbs
          ≤ (x * h1 ^ 2).natAbs + (y * h2 ^ 2).natAbs := Int.natAbs_sub_le _ _
        _ ≤ r * X ^ 2 + r * Y ^ 2 := add_le_add hx1 hy1
        _ = M := by rw [hM]; ring
    change (((x * h1 ^ 2 - y * h2 ^ 2).natAbs.divisors.card : ℝ)) ^ 4
        ≤ ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0)
    by_cases hm0 : (x * h1 ^ 2 - y * h2 ^ 2).natAbs = 0
    · have hz : ((x * h1 ^ 2 - y * h2 ^ 2).natAbs.divisors.card : ℝ) ^ 4 = 0 := by
        rw [hm0]; simp
      rw [hz]
      apply Finset.sum_nonneg; intro d _
      split_ifs <;> positivity
    · have hm1 : 1 ≤ (x * h1 ^ 2 - y * h2 ^ 2).natAbs := Nat.one_le_iff_ne_zero.mpr hm0
      have hzz : (x * h1 ^ 2 - y * h2 ^ 2) ≠ 0 := fun h => hm0 ((Int.natAbs_eq_zero).mpr h)
      have hb := tau4_le_sum_indicators_cube (m := (x * h1 ^ 2 - y * h2 ^ 2).natAbs) (M := M)
        hm1 hmM
      refine hb.trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro d _
      by_cases hd : d ∣ (x * h1 ^ 2 - y * h2 ^ 2).natAbs
      · have hc : (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0 :=
          ⟨(Int.natCast_dvd).mpr hd, hzz⟩
        rw [if_pos hd, if_pos hc]
        exact le_of_eq (by ring)
      · have hc : ¬ ((d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0) := by
          rintro ⟨h1', _⟩
          exact hd ((Int.natCast_dvd).mp h1')
        rw [if_neg hd, if_neg hc]
        exact le_of_eq (by ring)
  have hstep1 : Work.FIArea2.R6.uboxSum r X Y
      = ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2 := rfl
  have hstep2 : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2)
      ≤ ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum; intro x hx
    apply Finset.sum_le_sum; intro y hy
    apply Finset.sum_le_sum; intro h1 hh1
    apply Finset.sum_le_sum; intro h2 hh2
    exact key x hx y hy h1 hh1 h2 hh2
  have hstep3 : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0))
      = ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
          ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0) :=
    sum4_sum_comm _
  have hstep4 : (∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
          ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
            ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
              * (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                      then (1 : ℝ) else 0))
      = (2 : ℝ) ^ (20 : ℕ) *
          ∑ d ∈ (Finset.Icc 1 (Nat.sqrt M)).filter (fun d => d ^ 3 ≤ M),
            ((d.divisors.card : ℝ)) ^ 20 * ndCount d r X Y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    rw [pull_const4'' ((2 : ℝ) ^ (20 : ℕ) * ((d.divisors.card : ℝ)) ^ 20)
      (fun x y h1 h2 => if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
                          then (1 : ℝ) else 0)]
    have hsum : (∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        (if (d : ℤ) ∣ x * h1 ^ 2 - y * h2 ^ 2 ∧ x * h1 ^ 2 - y * h2 ^ 2 ≠ 0
          then (1 : ℝ) else 0)) = ndCount d r X Y := rfl
    rw [hsum]; ring
  calc Work.FIArea2.R6.uboxSum r X Y
      = ∑ x ∈ zPz r, ∑ y ∈ zPz r, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, T4 x y h1 h2 := hstep1
    _ ≤ _ := hstep2
    _ = _ := hstep3
    _ = _ := hstep4

end

end Work.FIArea2.R6
