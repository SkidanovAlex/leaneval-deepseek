import Mathlib
import Submission.Work.TMPuig.upperTri_decomp_fresh
import Submission.Work.TMContract.Defs

/-!
# Periodic upper-triangular decomposition of a degree-0 `SL(2,ℝ)` cocycle

Same statement as `upperTri_decomp_fresh`, but with the hypothesis that `B` is `1`-periodic;
the conclusion then carries the extra information that the gauge entries `ρ` and `σ` can be
chosen `1`-periodic as well.  The construction is the explicit one: `ρ y` is the norm of the
first column and `σ y` is the natural quadratic expression, both of which are manifestly
periodic when `B` is.
-/

open Work.TMContract

noncomputable section

namespace Work.TMPuig

theorem upperTri_decomp_periodic (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hper : ∀ x, B (x + 1) = B x) (hdet : ∀ x, (B x).det = 1)
    (hdeg : Work.TMContract.HasDegree B 0) :
    ∃ (η ρ σ : ℝ → ℝ), Continuous η ∧ (∀ x, η (x + 1) = η x) ∧
      Continuous ρ ∧ Continuous σ ∧ (∀ y, ρ (y + 1) = ρ y) ∧ (∀ y, σ (y + 1) = σ y) ∧
      (∀ y, 0 < ρ y) ∧
      (∀ y, B y = Work.TMContract.rot (η y) * !![ρ y, σ y; 0, 1 / ρ y]) := by
  obtain ⟨hBc, η, hηc, hηp, hη⟩ := hdeg
  have hη0 : ∀ x, η (x + 1) = η x := by
    intro x; have h := hηp x; simpa using h
  let ρ : ℝ → ℝ := fun y => Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2)
  let σ : ℝ → ℝ := fun y =>
    Real.cos (2 * Real.pi * η y) * B y 0 1 + Real.sin (2 * Real.pi * η y) * B y 1 1
  refine ⟨η, ρ, σ, hηc, hη0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun y => Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2))
    fun_prop
  · change Continuous (fun y =>
      Real.cos (2 * Real.pi * η y) * B y 0 1 + Real.sin (2 * Real.pi * η y) * B y 1 1)
    fun_prop
  · intro y
    dsimp only [ρ]
    rw [hper y]
  · intro y
    dsimp only [σ]
    rw [hη0 y, hper y]
  · intro y
    obtain ⟨r, hr, h1, h2⟩ := hη y
    have hsq : (B y 0 0) ^ 2 + (B y 1 0) ^ 2 = r ^ 2 := by
      rw [h1, h2]; nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * η y)]
    change 0 < Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2)
    rw [hsq, Real.sqrt_sq hr.le]; exact hr
  · intro y
    obtain ⟨r, hr, h1, h2⟩ := hη y
    have hsq : (B y 0 0) ^ 2 + (B y 1 0) ^ 2 = r ^ 2 := by
      rw [h1, h2]; nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * η y)]
    have hρy : ρ y = r := by
      change Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2) = r
      rw [hsq, Real.sqrt_sq hr.le]
    have hdet' : B y 0 0 * B y 1 1 - B y 0 1 * B y 1 0 = 1 := by
      have h := hdet y
      rwa [Matrix.det_fin_two] at h
    rw [one_div]
    exact (rot_mul_upper_eq (B := B y) (η := η y) (ρ := ρ y) (σ := σ y)
      (by rw [hρy]; exact hr) (by rw [hρy]; exact h1) (by rw [hρy]; exact h2)
      hdet' rfl).symm

end Work.TMPuig
