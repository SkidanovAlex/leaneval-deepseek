import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.small_divisor_tau_le
import Submission.Work.FIArea2.Count.sum_int_natAbs_le

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `(d:ℤ) ∣ m ↔ d ∣ m.natAbs`. -/
lemma int_dvd_iff_natAbs (d : ℕ) (m : ℤ) : (d : ℤ) ∣ m ↔ d ∣ m.natAbs := by
  constructor
  · intro h
    have h2 : ((d : ℤ).natAbs) ∣ m.natAbs := (Int.natAbs_dvd_natAbs (a := ((d:ℤ))) (b := m)).mpr h
    simpa using h2
  · intro h
    have h2 : ((d : ℤ).natAbs) ∣ m.natAbs := by simpa using h
    exact (Int.natAbs_dvd_natAbs (a := ((d:ℤ))) (b := m)).mp h2

/-- `τ(m n²)⁴ ≤ τ(m)⁴ τ(n)⁸`. -/
lemma tau_mul_sq_pow4_le (m n : ℕ) :
    (((m * n ^ 2).divisors.card : ℝ)) ^ 4
      ≤ (((m.divisors.card : ℝ)) ^ 4) * (((n.divisors.card : ℝ)) ^ 8) := by
  have h1 : (((m * n ^ 2).divisors.card : ℝ))
      ≤ ((m.divisors.card : ℝ)) * (((n ^ 2).divisors.card : ℝ)) := by
    have h : (m * n ^ 2).divisors.card ≤ m.divisors.card * (n ^ 2).divisors.card := by
      rw [Nat.divisors_mul]; exact Finset.card_mul_le
    exact_mod_cast h
  have h2 : (((n ^ 2).divisors.card : ℝ)) ≤ ((n.divisors.card : ℝ)) ^ 2 := by
    have h := Work.FIArea2.tauR_mul_le n n
    have hn : n * n = n ^ 2 := by ring
    rw [hn] at h
    simpa [Work.FIArea2.tauR, pow_two] using h
  calc (((m * n ^ 2).divisors.card : ℝ)) ^ 4
      ≤ (((m.divisors.card : ℝ)) * ((n.divisors.card : ℝ)) ^ 2) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = (((m.divisors.card : ℝ)) ^ 4) * (((n.divisors.card : ℝ)) ^ 8) := by ring

/-- `([-N,N] : Finset ℤ) = {0} ∪ ([-N,N] \ {0})`. -/
lemma Icc_int_eq_insert (N : ℕ) :
    Finset.Icc (-(N : ℤ)) (N : ℤ)
      = insert 0 ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun u => u ≠ 0)) := by
  ext u
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    by_cases hu : u = 0
    · exact Or.inl hu
    · exact Or.inr ⟨h, hu⟩
  · rintro (rfl | ⟨h, _⟩)
    · constructor <;> simp
    · exact h

/-- The cardinality of the integer box `[-N,N]`. -/
lemma card_Icc_int (N : ℕ) : (((Finset.Icc (-(N : ℤ)) (N : ℤ))).card : ℝ) = 2 * N + 1 := by
  rw [Int.card_Icc]
  have hz : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hz, Int.toNat_natCast]; push_cast; ring

lemma sum_box_tau8_le (Y : ℕ) :
    (∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ), (((h2.natAbs).divisors.card : ℝ)) ^ 8)
      ≤ 2 * ∑ b ∈ Finset.Icc 1 Y, (((b).divisors.card : ℝ)) ^ 8 := by
  have hsplit : (∑ h2 ∈ Finset.Icc (-(Y : ℤ)) (Y : ℤ), (((h2.natAbs).divisors.card : ℝ)) ^ 8)
      = ∑ h2 ∈ (Finset.Icc (-(Y : ℤ)) (Y : ℤ)).filter (fun u => u ≠ 0),
          (((h2.natAbs).divisors.card : ℝ)) ^ 8 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro u hu hnot
    have hu0 : u = 0 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hu, h⟩)
    rw [hu0]; simp [Nat.divisors_zero]
  rw [hsplit]
  exact Work.FIArea2.Count.sum_int_natAbs_le Y (fun n => (((n).divisors.card : ℝ)) ^ 8)
    (fun n => by positivity)

lemma sum_vbox_abs_tau4_le (R : ℕ) :
    (∑ u ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun u => u ≠ 0),
        (u.natAbs : ℝ) * (((u.natAbs).divisors.card : ℝ)) ^ 4)
      ≤ 2 * (R : ℝ) * ∑ a ∈ Finset.Icc 1 R, (((a).divisors.card : ℝ)) ^ 4 := by
  have h := Work.FIArea2.Count.sum_int_natAbs_le R
    (fun n => (n : ℝ) * (((n).divisors.card : ℝ)) ^ 4) (fun n => by positivity)
  refine le_trans h ?_
  have h1 : (∑ a ∈ Finset.Icc 1 R, (a:ℝ) * (((a).divisors.card : ℝ)) ^ 4)
      ≤ (R:ℝ) * ∑ a ∈ Finset.Icc 1 R, (((a).divisors.card : ℝ)) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a ha => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (Finset.mem_Icc.mp ha).2
  calc 2 * ∑ a ∈ Finset.Icc 1 R, (a:ℝ) * (((a).divisors.card : ℝ)) ^ 4
      ≤ 2 * ((R:ℝ) * ∑ a ∈ Finset.Icc 1 R, (((a).divisors.card : ℝ)) ^ 4) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 2 * (R : ℝ) * ∑ a ∈ Finset.Icc 1 R, (((a).divisors.card : ℝ)) ^ 4 := by ring

end

end Work.FIArea2.Count
