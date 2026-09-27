import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.circleIntegral_conj
import Submission.Work.KT.FP.pResA_idem

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# `Work.KT.FP.proj_identities` — the basic identities of the pencil projection

For a complex Banach algebra `R` and the pencil projection
`pProj A B ρ = (2πi)⁻¹ ∮_{|z|=ρ} (z•A + B)⁻¹ A dz` of `Work.KT.FP.PencilDefs`, we prove the
three identities

* `pProj (L*A) (L*B) ρ = pProj A B ρ` for a unit `L` (the projection only depends on the pencil up
  to a left factor);
* `pProj (L*A*L⁻¹) (L*B*L⁻¹) ρ = L * pProj A B ρ * L⁻¹` for a unit `L` (conjugation equivariance);
* `pProj E (1 - E) ρ = E` for an idempotent `E` and `ρ > 0` (the pencil `z ↦ zE + (1-E)` has its
  "inside" spectral projection equal to `E`).

The proof splits the identities into the pointwise resolvent identities (proved here) and the
circle-integral manipulation: `Work.KT.FP.circleIntegral_conj` (conjugation commutes with the
contour integral) and `Work.KT.FP.pResA_idem` (the pointwise identity `pResA E (1-E) z = z⁻¹ • E`
for `z ≠ 0`).
-/

namespace Work.KT.FP

open MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The pencil resolvent-integrand is unchanged by multiplying the pencil on the left by a unit,
because the extra factor cancels against its inverse. -/
theorem pResA_mul_unit (A B L : R) (hL : IsUnit L) (z : ℂ) :
    pResA (L * A) (L * B) z = pResA A B z := by
  unfold pResA pRes
  have hsum : z • (L * A) + L * B = L * (z • A + B) := by
    rw [← mul_smul_comm z L A, mul_add]
  rw [hsum, Ring.inverse_mul (Or.inl hL)]
  simp only [mul_assoc]
  rw [Ring.inverse_mul_cancel_left L A hL]

/-- Conjugation equivariance of the pencil resolvent-integrand. -/
theorem pResA_conj (A B L : R) (hL : IsUnit L) (z : ℂ) :
    pResA (L * A * Ring.inverse L) (L * B * Ring.inverse L) z
      = L * pResA A B z * Ring.inverse L := by
  unfold pResA pRes
  have hsum : z • (L * A * Ring.inverse L) + L * B * Ring.inverse L
      = L * (z • A + B) * Ring.inverse L := by
    rw [← smul_mul_assoc z (L * A) (Ring.inverse L), ← mul_smul_comm z L A, ← add_mul,
      ← mul_add]
  have hinv : Ring.inverse (L * (z • A + B) * Ring.inverse L)
      = L * Ring.inverse (z • A + B) * Ring.inverse L := by
    rw [mul_assoc, Ring.inverse_mul (Or.inl hL)]
    rw [Ring.inverse_mul (Or.inr (IsUnit.ringInverse hL))]
    rw [Ring.inverse_inverse hL]
  rw [hsum, hinv]
  simp only [mul_assoc]
  rw [Ring.inverse_mul_cancel_left L (A * Ring.inverse L) hL]

/-- The contour integral of the pencil resolvent-integrand is unchanged by a left factor that is a
unit. -/
theorem pCirc_mul_unit (A B L : R) (hL : IsUnit L) (ρ : ℝ) :
    pCirc (L * A) (L * B) ρ = pCirc A B ρ := by
  have h : (fun z => pResA (L * A) (L * B) z) = fun z => pResA A B z :=
    funext fun z => pResA_mul_unit A B L hL z
  simp only [pCirc]
  rw [h]

/-- Conjugation equivariance of the contour integral of the pencil. -/
theorem pCirc_conj (A B L : R) (hL : IsUnit L) (ρ : ℝ) :
    pCirc (L * A * Ring.inverse L) (L * B * Ring.inverse L) ρ
      = L * pCirc A B ρ * Ring.inverse L := by
  have h : (fun z => pResA (L * A * Ring.inverse L) (L * B * Ring.inverse L) z)
      = fun z => L * pResA A B z * Ring.inverse L :=
    funext fun z => pResA_conj A B L hL z
  rw [pCirc, h, pCirc]
  exact circleIntegral_conj L hL (fun z => pResA A B z) 0 ρ

/-- The contour integral for the idempotent pencil `z ↦ zE + (1 - E)`: on `|z| = ρ` (`ρ > 0`) the
resolvent-integrand equals `z⁻¹ • E`, and `∮_{|z|=ρ} z⁻¹ dz = 2πi`. -/
theorem pCirc_idem (E : R) (hE : E * E = E) (ρ : ℝ) (hρ : 0 < ρ) :
    pCirc E (1 - E) ρ = (2 * Real.pi * Complex.I) • E := by
  rw [pCirc, circleIntegral.integral_congr hρ.le (fun z hz => ?_)]
  · rw [circleIntegral.integral_smul_const]
    congr 1
    simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) hρ.ne'
  · rw [Metric.mem_sphere, dist_zero_right] at hz
    refine pResA_idem E hE z (fun h => ?_)
    rw [h] at hz
    simp only [norm_zero] at hz
    exact hρ.ne' hz.symm

theorem proj_identities {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] :
    (∀ (A B L : R) (hL : IsUnit L) (ρ : ℝ), pProj (L * A) (L * B) ρ = pProj A B ρ) ∧
    (∀ (A B L : R) (hL : IsUnit L) (ρ : ℝ),
      pProj (L * A * Ring.inverse L) (L * B * Ring.inverse L) ρ
        = L * pProj A B ρ * Ring.inverse L) ∧
    (∀ (E : R) (hE : E * E = E) (ρ : ℝ) (hρ : 0 < ρ), pProj E (1 - E) ρ = E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B L hL ρ
    simp only [pProj]
    rw [pCirc_mul_unit A B L hL ρ]
  · intro A B L hL ρ
    simp only [pProj]
    rw [pCirc_conj A B L hL ρ, mul_smul_comm, smul_mul_assoc]
  · intro E hE ρ hρ
    have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    simp only [pProj]
    rw [pCirc_idem E hE ρ hρ, smul_smul, inv_mul_cancel₀ h2piI, one_smul]

end

end Work.KT.FP
