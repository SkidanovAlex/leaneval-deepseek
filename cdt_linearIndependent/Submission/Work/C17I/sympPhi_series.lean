import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.CPull.evp_sympPhi

/-!
# The power series of the symmetrization involution `φ = X/(X−1)` converges to `z/(z−1)`

`Submission.CDT.sympPhi = X/(X−1)` has coefficients `0` at `0` and `−1` from `1` on, so its
evaluating series on the open unit disc is `Σ_{n≥1} (−1) zⁿ = z/(z−1)`, and the associated
dominating series `Σ ‖cₙ‖ ρⁿ = Σ_{n≥1} ρⁿ = ρ/(1−ρ)` for `ρ ∈ [0,1)`.

Both statements are recorded here as `HasSum` (rather than `tsum`) because the downstream
estimates need summability together with the value.
-/

namespace Work.C17I

open PowerSeries

/-- The rational coefficients of `φ = X/(X−1)` cast to `ℂ`: `0` at `0`, `−1` elsewhere. -/
lemma coeff_sympPhi_cast (n : ℕ) :
    ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) = if n = 0 then 0 else -1 := by
  rw [Work.CPull.coeff_sympPhi_eq n]; split <;> simp

/-- The norms of the coefficients of `φ`: `0` at `0`, `1` elsewhere. -/
lemma norm_coeff_sympPhi (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖ = if n = 0 then (0:ℝ) else 1 := by
  rw [coeff_sympPhi_cast n]; split <;> simp

theorem sympPhi_series :
    (∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n : ℕ => ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ n) (z / (z - 1))) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → HasSum (fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ρ ^ n) (ρ / (1 - ρ))) := by
  constructor
  · intro z hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    have hgeo : HasSum (fun n : ℕ => z ^ n) ((1 - z)⁻¹) := hasSum_geometric_of_norm_lt_one hz
    have hind : HasSum (fun n : ℕ => if n = 0 then (1:ℂ) else 0) 1 := by
      have h := hasSum_single (f := fun n : ℕ => if n = 0 then (1:ℂ) else 0) 0
        (by intro b hb; simp [hb])
      simpa using h
    have hsum := hgeo.neg.add hind
    have hval : -((1 - z)⁻¹) + 1 = z / (z - 1) := by
      have : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
      field_simp
      ring
    rw [hval] at hsum
    refine hsum.congr_fun (fun n => ?_)
    rw [coeff_sympPhi_cast n]
    rcases eq_or_ne n 0 with h | h
    · subst h; simp
    · simp [h]
  · intro ρ hρ0 hρ1
    have hρnorm : ‖ρ‖ < 1 := by rwa [Real.norm_of_nonneg hρ0]
    have hgeo : HasSum (fun n : ℕ => ρ ^ n) ((1 - ρ)⁻¹) := hasSum_geometric_of_norm_lt_one hρnorm
    have hind : HasSum (fun n : ℕ => if n = 0 then (1:ℝ) else 0) 1 := by
      have h := hasSum_single (f := fun n : ℕ => if n = 0 then (1:ℝ) else 0) 0
        (by intro b hb; simp [hb])
      simpa using h
    have hsum := hgeo.sub hind
    have hval : (1 - ρ)⁻¹ - 1 = ρ / (1 - ρ) := by
      have : (1 - ρ) ≠ 0 := by linarith
      field_simp
      ring
    rw [hval] at hsum
    refine hsum.congr_fun (fun n => ?_)
    rw [norm_coeff_sympPhi n]
    rcases eq_or_ne n 0 with h | h
    · subst h; simp
    · simp [h]

end Work.C17I
