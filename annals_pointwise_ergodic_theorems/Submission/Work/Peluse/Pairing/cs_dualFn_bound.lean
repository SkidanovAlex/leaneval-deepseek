import Mathlib
import Submission.Work.Peluse.Peel.tsum_sq_eq_sum_symIcc

namespace Work.Peluse.Pairing

/-- Cauchy–Schwarz for the dual pairing: if `U` is supported in `[-R, R]` and `‖V‖ ≤ 1` pointwise
then `|∑_z U z V z|² ≤ |[-R,R]| · ∑_z ‖U z‖²`. -/
theorem cs_dualFn_bound {R : ℕ} (U V : ℤ → ℂ)
    (hU : Work.Peluse.SupportIn U R) (hV : ∀ z : ℤ, ‖V z‖ ≤ 1) :
    ‖∑' z : ℤ, U z * V z‖ ^ 2
      ≤ (((Work.Peluse.symIcc R).card : ℕ) : ℝ) * ∑' z : ℤ, ‖U z‖ ^ 2 := by
  classical
  have hmem : ∀ z : ℤ, z ∈ Work.Peluse.symIcc R ↔ z.natAbs ≤ R := by
    intro z
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have h : (z.natAbs : ℤ) ≤ (R : ℤ) := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr ⟨h1, h2⟩
      exact_mod_cast h
    · intro h
      have h' : (z.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast h
      rw [Int.natCast_natAbs] at h'
      exact abs_le.mp h'
  have htsum : ∑' z : ℤ, U z * V z = ∑ z ∈ Work.Peluse.symIcc R, U z * V z := by
    rw [tsum_eq_sum (s := Work.Peluse.symIcc R)]
    intro z hz
    have hle : R < z.natAbs := by
      by_contra hcon
      exact hz ((hmem z).mpr (not_lt.mp hcon))
    rw [hU z hle, zero_mul]
  rw [htsum]
  set S : Finset ℤ := Work.Peluse.symIcc R with hS
  have h1 : ‖∑ z ∈ S, U z * V z‖ ≤ ∑ z ∈ S, ‖U z‖ * ‖V z‖ := by
    calc ‖∑ z ∈ S, U z * V z‖ ≤ ∑ z ∈ S, ‖U z * V z‖ := norm_sum_le _ _
      _ = ∑ z ∈ S, ‖U z‖ * ‖V z‖ := by simp
  have h2 : (∑ z ∈ S, ‖U z‖ * ‖V z‖) ^ 2 ≤ (∑ z ∈ S, ‖U z‖ ^ 2) * ∑ z ∈ S, ‖V z‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S (fun z => ‖U z‖) (fun z => ‖V z‖)
  have hUsum : (∑ z ∈ S, ‖U z‖ ^ 2) = ∑' z : ℤ, ‖U z‖ ^ 2 := by
    rw [hS]
    exact (Work.Peluse.Peel.tsum_sq_eq_sum_symIcc (fun z => ‖U z‖) (le_refl R)
      (fun x hx => by rw [hU x hx]; simp)).symm
  have hVsum : (∑ z ∈ S, ‖V z‖ ^ 2) ≤ ((S.card : ℕ) : ℝ) := by
    calc ∑ z ∈ S, ‖V z‖ ^ 2 ≤ ∑ _z ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro z _
          nlinarith [norm_nonneg (V z), hV z]
      _ = ((S.card : ℕ) : ℝ) := by simp
  have hFnn : (0 : ℝ) ≤ ∑ z ∈ S, ‖U z‖ ^ 2 := by positivity
  calc ‖∑ z ∈ S, U z * V z‖ ^ 2
      ≤ (∑ z ∈ S, ‖U z‖ * ‖V z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ z ∈ S, ‖U z‖ ^ 2) * ∑ z ∈ S, ‖V z‖ ^ 2 := h2
    _ ≤ (∑ z ∈ S, ‖U z‖ ^ 2) * ((S.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hVsum hFnn
    _ = ((S.card : ℕ) : ℝ) * ∑' z : ℤ, ‖U z‖ ^ 2 := by rw [hUsum]; ring

end Work.Peluse.Pairing
