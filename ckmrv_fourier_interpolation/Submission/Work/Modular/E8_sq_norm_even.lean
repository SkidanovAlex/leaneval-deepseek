import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.E8_eight_dvd_sum_sq

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-- Membership in `E8` can be witnessed by an integer vector `d` with `2 * x i = d i`: since the
coordinates of `x` are pairwise congruent modulo `1`, the integers `d i` all have the same parity,
and since the coordinate sum of `x` is even, `4 ∣ ∑ i, d i`. -/
theorem exists_int_coords_of_mem_E8 {x : EuclideanSpace ℝ (Fin 8)} (hx : x ∈ E8) :
    ∃ d : Fin 8 → ℤ, (∀ i, 2 * x.ofLp i = (d i : ℝ)) ∧
      (∀ i, ∃ m : ℤ, d i - d 0 = 2 * m) ∧ (4 : ℤ) ∣ ∑ i, d i := by
  rw [mem_E8] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  choose d hd using h1
  refine ⟨d, hd, ?_, ?_⟩
  · intro i
    obtain ⟨m, hm⟩ := h2 i 0
    refine ⟨m, ?_⟩
    have : ((d i - d 0 : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by
      push_cast
      linarith [hd i, hd 0, hm]
    exact_mod_cast this
  · obtain ⟨m, hm⟩ := h3
    refine ⟨m, ?_⟩
    have hcast : ((∑ i, d i : ℤ) : ℝ) = ((4 * m : ℤ) : ℝ) := by
      push_cast
      calc ∑ i, ((d i : ℤ) : ℝ) = ∑ i, 2 * x.ofLp i :=
            Finset.sum_congr rfl (fun i _ => (hd i).symm)
        _ = 2 * ∑ i, x.ofLp i := by rw [Finset.mul_sum]
        _ = 4 * (m : ℝ) := by rw [hm]; ring
    exact_mod_cast hcast

/-- If the integer vector `d` encodes `2 * x` (coordinatewise), then `4 * ‖x‖ ^ 2` is the sum of
the squares of the coordinates of `d`. -/
theorem E8_four_mul_norm_sq {x : EuclideanSpace ℝ (Fin 8)} {d : Fin 8 → ℤ}
    (hd : ∀ i, 2 * x.ofLp i = (d i : ℝ)) :
    4 * ‖x‖ ^ 2 = ((∑ i, d i ^ 2 : ℤ) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hterm : ∀ i, 4 * x.ofLp i ^ 2 = ((d i ^ 2 : ℤ) : ℝ) := by
    intro i
    have h : x.ofLp i = (d i : ℝ) / 2 := by linarith [hd i]
    rw [h]; push_cast; ring
  calc 4 * ∑ i, x.ofLp i ^ 2 = ∑ i, 4 * x.ofLp i ^ 2 := by rw [Finset.mul_sum]
    _ = ∑ i, ((d i ^ 2 : ℤ) : ℝ) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ((∑ i, d i ^ 2 : ℤ) : ℝ) := by push_cast; rfl

/-- Every vector of the `E₈` lattice has even squared length. -/
theorem E8_sq_norm_even : IsEvenSubmodule E8 := by
  intro x hx
  obtain ⟨d, hd, hpar, h4⟩ := exists_int_coords_of_mem_E8 hx
  obtain ⟨t, ht⟩ := E8_eight_dvd_sum_sq hpar h4
  -- `4 * ‖x‖ ^ 2 = 8 * t`, so `‖x‖ ^ 2 = 2 * t`, and `t ≥ 0`.
  have hnorm : 4 * ‖x‖ ^ 2 = 8 * (t : ℝ) := by
    rw [E8_four_mul_norm_sq hd, ht]; push_cast; ring
  have ht0R : (0 : ℝ) ≤ (t : ℝ) := by
    have h1 : (0 : ℝ) ≤ ((∑ i, d i ^ 2 : ℤ) : ℝ) := by
      push_cast
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rw [← E8_four_mul_norm_sq hd, hnorm] at h1
    linarith
  have ht0 : 0 ≤ t := by exact_mod_cast ht0R
  refine ⟨t.toNat, ?_⟩
  have hk : ((t.toNat : ℕ) : ℝ) = (t : ℝ) := by
    rw [← Int.toNat_of_nonneg ht0]
    push_cast
    rfl
  rw [hk]
  linarith

end Work.Modular
