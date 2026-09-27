import Mathlib
import Submission.Work.Mostow.horoballOverlapCriterion
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-- Level separation: two distinct horoballs of a pairwise disjoint family whose levels satisfy
`|ht ξ| ≤ R` and `|ht η| ≤ R` have their base points at Euclidean distance at least `2 * exp (-R)`.

Hint: `horoballOverlapCriterion` turns disjointness into `2 * exp (ht ξ + ht η) ≤ 1 - ⟪ξ,η⟫`, and
`‖ξ - η‖^2 = 2 - 2 * ⟪ξ,η⟫ = 2 * (1 - ⟪ξ,η⟫)` for `ξ, η ∈ Sph n`, so `dist ξ η^2 ≥ 4 * exp (-2R)`
using `ht ξ ≥ -R`, `ht η ≥ -R`. -/
theorem horoballLevelSeparation (n : ℕ) (P : Set (Submission.Mostow.E n)) (ht : Submission.Mostow.E n → ℝ)
    (hPsub : P ⊆ Submission.Mostow.Sph n)
    (hdisj : P.Pairwise (fun ξ η => Disjoint (Submission.Mostow.horoball ξ (ht ξ))
      (Submission.Mostow.horoball η (ht η))))
    {R : ℝ} {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ P) (hη : η ∈ P) (hne : ξ ≠ η)
    (hξR : |ht ξ| ≤ R) (hηR : |ht η| ≤ R) :
    2 * Real.exp (-R) ≤ dist ξ η := by
  have hξS : ξ ∈ Sph n := hPsub hξ
  have hηS : η ∈ Sph n := hPsub hη
  -- Disjointness at the pair `(ξ, η)`, and hence no common point.
  have hd := hdisj hξ hη hne
  have hno : ¬ ∃ u, u ∈ horoball ξ (ht ξ) ∧ u ∈ horoball η (ht η) := by
    rintro ⟨u, hu1, hu2⟩
    exact (Set.disjoint_left.mp hd hu1) hu2
  -- The overlap criterion, contraposed.
  have hle : 2 * Real.exp (ht ξ + ht η) ≤ 1 - inner ℝ ξ η := by
    by_contra h
    exact hno ((horoballOverlapCriterion n ξ η hξS hηS (ht ξ) (ht η)).mpr (not_le.mp h))
  -- The level bounds give `exp (-R) ≤ exp (ht ξ)`, `exp (-R) ≤ exp (ht η)`.
  have hξle : -R ≤ ht ξ := (abs_le.mp hξR).1
  have hηle : -R ≤ ht η := (abs_le.mp hηR).1
  have hexpξ : Real.exp (-R) ≤ Real.exp (ht ξ) := Real.exp_le_exp.mpr hξle
  have hexpη : Real.exp (-R) ≤ Real.exp (ht η) := Real.exp_le_exp.mpr hηle
  have hexp2 : Real.exp (-R) * Real.exp (-R) ≤ Real.exp (ht ξ) * Real.exp (ht η) :=
    mul_le_mul hexpξ hexpη (Real.exp_pos _).le (le_of_lt (Real.exp_pos _))
  rw [Real.exp_add] at hle
  have hkey : 2 * (Real.exp (-R) * Real.exp (-R)) ≤ 1 - inner ℝ ξ η := by linarith
  -- Euclidean distance on the unit sphere.
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξS
  have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hηS
  have hnorm : ‖ξ - η‖ ^ 2 = 2 * (1 - inner ℝ ξ η) := by
    rw [norm_sub_sq_real, hξn, hηn]
    ring
  have h4 : (2 * Real.exp (-R)) ^ 2 ≤ ‖ξ - η‖ ^ 2 := by
    rw [hnorm]
    nlinarith [hkey]
  rw [dist_eq_norm]
  have h2e : (0 : ℝ) ≤ 2 * Real.exp (-R) := by positivity
  have h := sq_le_sq.mp h4
  rwa [abs_of_nonneg h2e, abs_of_nonneg (norm_nonneg _)] at h

end

end Work.Mostow
