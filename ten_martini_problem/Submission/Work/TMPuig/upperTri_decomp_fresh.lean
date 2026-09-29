import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RotBasics.Defs

/-!
# Upper-triangular decomposition of a degree-0 `SL(2,ℝ)` cocycle

`HasDegree B 0` says that the first column `B x e₁` has a continuous polar angle `η`
(in turns), `η(x+1) = η x`.  Writing `B x = ρ x (cos 2πη x, sin 2πη x)` for the first
column, the determinant-one condition identifies the second column, so that

  `B x = rot (η x) * !![ρ x, σ x; 0, (ρ x)⁻¹]`

with `ρ` the (strictly positive) radius of the first column and `σ` a suitable
continuous function.  This is the "gauge" normal form used in the Puig argument.
-/

open Work.TMContract

noncomputable section

namespace Work.TMPuig

/-- Algebra behind `upperTri_decomp_fresh`: a determinant-one matrix whose first column is
`(ρ cos θ, ρ sin θ)` factors as `rot (θ/2π)` times an upper-triangular matrix with diagonal
`(ρ, ρ⁻¹)` and (0,1)-entry `cos θ · B 0 1 + sin θ · B 1 1`.  Here `θ = 2πη`. -/
lemma rot_mul_upper_eq {B : Matrix (Fin 2) (Fin 2) ℝ} {η ρ σ : ℝ} (hρ : 0 < ρ)
    (h00 : B 0 0 = ρ * Real.cos (2 * Real.pi * η))
    (h10 : B 1 0 = ρ * Real.sin (2 * Real.pi * η))
    (hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1)
    (hσ : σ = Real.cos (2 * Real.pi * η) * B 0 1 + Real.sin (2 * Real.pi * η) * B 1 1) :
    rot η * !![ρ, σ; 0, ρ⁻¹] = B := by
  have hX : Real.cos (2 * Real.pi * η) * B 1 1 - Real.sin (2 * Real.pi * η) * B 0 1 = ρ⁻¹ := by
    have h : ρ * (Real.cos (2 * Real.pi * η) * B 1 1 - Real.sin (2 * Real.pi * η) * B 0 1) = 1 := by
      have h' := hdet
      rw [h00, h10] at h'
      nlinarith [h']
    calc Real.cos (2 * Real.pi * η) * B 1 1 - Real.sin (2 * Real.pi * η) * B 0 1
        = ρ⁻¹ * (ρ * (Real.cos (2 * Real.pi * η) * B 1 1 - Real.sin (2 * Real.pi * η) * B 0 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hρ), one_mul]
      _ = ρ⁻¹ := by rw [h, mul_one]
  have hP : Real.cos (2 * Real.pi * η) ^ 2 + Real.sin (2 * Real.pi * η) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, h00, h10, hσ]
  · ring
  · linear_combination (B 0 1) * hP + (Real.sin (2 * Real.pi * η)) * hX
  · ring
  · linear_combination (B 1 1) * hP - (Real.cos (2 * Real.pi * η)) * hX

theorem upperTri_decomp_fresh {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : ∀ x, (B x).det = 1) (hdeg : Work.TMContract.HasDegree B 0) :
    ∃ (η ρ σ : ℝ → ℝ), Continuous η ∧ (∀ x, η (x + 1) = η x) ∧ Continuous ρ ∧
      Continuous σ ∧ (∀ y, 0 < ρ y) ∧
      (∀ y, B y = Work.TMContract.rot (η y) * !![ρ y, σ y; 0, (ρ y)⁻¹]) := by
  obtain ⟨hBc, η, hηc, hηp, hη⟩ := hdeg
  let ρ : ℝ → ℝ := fun y => Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2)
  let σ : ℝ → ℝ := fun y => Real.cos (2 * Real.pi * η y) * B y 0 1 + Real.sin (2 * Real.pi * η y) * B y 1 1
  refine ⟨η, ρ, σ, hηc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simpa using hηp x
  · change Continuous (fun y => Real.sqrt ((B y 0 0) ^ 2 + (B y 1 0) ^ 2))
    fun_prop
  · change Continuous (fun y => Real.cos (2 * Real.pi * η y) * B y 0 1 + Real.sin (2 * Real.pi * η y) * B y 1 1)
    fun_prop
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
    change B y = rot (η y) * !![ρ y, σ y; 0, (ρ y)⁻¹]
    exact (rot_mul_upper_eq (B := B y) (η := η y) (ρ := ρ y) (σ := σ y)
      (by rw [hρy]; exact hr) (by rw [hρy]; exact h1) (by rw [hρy]; exact h2) hdet' rfl).symm

end Work.TMPuig
