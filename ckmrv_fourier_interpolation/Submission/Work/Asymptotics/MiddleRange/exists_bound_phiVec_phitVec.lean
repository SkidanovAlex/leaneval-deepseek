import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.MiddleRange

/-! ## Continuity of the building blocks of `φ⃗` and `φ̃⃗`

The `φ⃗` coordinates are built from `τ` and `E₂`; the `φ̃⃗` coordinates from `z²` and
`(E₂|₂S)(z) = E₂(z) - 6i/(π z)`.  Continuity of all of these is what makes them
bounded on compact sets. -/

/-- `E₂` is continuous on `ℍ` (it lies in `𝒫`). -/
lemma continuous_E2Fun_uhp : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E2Fun τ) :=
  Work.Kernels.ClassicalFacts.E2Fun_mem_InP.1.continuous

/-- `(E₂|₂S)(z) = E₂(z) - 6i/(π z)` is continuous on `ℍ`. -/
lemma continuous_E2S : Continuous (fun z : UpperHalfPlane => Work.Kernels.E2S z) := by
  have h : (fun z : UpperHalfPlane => Work.Kernels.E2S z) =
      fun z : UpperHalfPlane =>
        Work.Kernels.E2Fun z - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ)) := by
    funext z; exact Work.Kernels.TildeFacts.E2S_eq z
  rw [h]
  refine Continuous.sub continuous_E2Fun_uhp ?_
  refine continuous_const.div (continuous_const.mul continuous_coe) ?_
  intro z
  exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    (Work.Kernels.KernelFacts.kpc_tau_ne_zero z)

lemma continuous_phiVec_0 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 0) =
      fun τ : UpperHalfPlane => (τ : ℂ) := by
    funext τ; rfl
  rw [h]; exact continuous_coe

lemma continuous_phiVec_1 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 1) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 1) =
      fun τ : UpperHalfPlane =>
        (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := by
    funext τ; rfl
  rw [h]
  exact (continuous_coe.mul continuous_E2Fun_uhp).sub continuous_const

lemma continuous_phiVec_2 : Continuous (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 2) := by
  have h : (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ 2) =
      fun τ : UpperHalfPlane =>
        (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 -
          (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ := by
    funext τ; rfl
  rw [h]
  exact (continuous_coe.mul (continuous_E2Fun_uhp.pow 2)).sub
    (continuous_const.mul continuous_E2Fun_uhp)

lemma continuous_phitVec_0 : Continuous (fun z : UpperHalfPlane => Work.Kernels.phitVec z 0) := by
  have h : (fun z : UpperHalfPlane => Work.Kernels.phitVec z 0) =
      fun z : UpperHalfPlane => (z : ℂ) ^ 2 := by
    funext z; rfl
  rw [h]; exact continuous_coe.pow 2

lemma continuous_phitVec_1 : Continuous (fun z : UpperHalfPlane => Work.Kernels.phitVec z 1) := by
  have h : (fun z : UpperHalfPlane => Work.Kernels.phitVec z 1) =
      fun z : UpperHalfPlane => (z : ℂ) ^ 2 * Work.Kernels.E2S z := by
    funext z; rfl
  rw [h]; exact (continuous_coe.pow 2).mul continuous_E2S

lemma continuous_phitVec_2 : Continuous (fun z : UpperHalfPlane => Work.Kernels.phitVec z 2) := by
  have h : (fun z : UpperHalfPlane => Work.Kernels.phitVec z 2) =
      fun z : UpperHalfPlane => (z : ℂ) ^ 2 * (Work.Kernels.E2S z) ^ 2 := by
    funext z; rfl
  rw [h]; exact (continuous_coe.pow 2).mul (continuous_E2S.pow 2)

/-- The basis vectors `phiVec` (built from `τ` and `E₂`) and `phitVec`
(`z²`, `z²(E₂|₂S)(z)`, `z²((E₂|₂S)(z))²`) are bounded on compact sets. -/
theorem exists_bound_phiVec_phitVec {S T : Set UpperHalfPlane} (hS : IsCompact S) (hT : IsCompact T) :
    (∃ P : ℝ, 0 < P ∧ ∀ τ ∈ S, ∀ i : Fin 3, ‖Work.Kernels.phiVec τ i‖ ≤ P) ∧
    (∃ Q : ℝ, 0 < Q ∧ ∀ z ∈ T, ∀ j : Fin 3, ‖Work.Kernels.phitVec z j‖ ≤ Q) := by
  obtain ⟨P0, hP0⟩ := hS.exists_bound_of_continuousOn continuous_phiVec_0.continuousOn
  obtain ⟨P1, hP1⟩ := hS.exists_bound_of_continuousOn continuous_phiVec_1.continuousOn
  obtain ⟨P2, hP2⟩ := hS.exists_bound_of_continuousOn continuous_phiVec_2.continuousOn
  obtain ⟨Q0, hQ0⟩ := hT.exists_bound_of_continuousOn continuous_phitVec_0.continuousOn
  obtain ⟨Q1, hQ1⟩ := hT.exists_bound_of_continuousOn continuous_phitVec_1.continuousOn
  obtain ⟨Q2, hQ2⟩ := hT.exists_bound_of_continuousOn continuous_phitVec_2.continuousOn
  refine ⟨⟨|P0| + |P1| + |P2| + 1, by positivity, ?_⟩,
          ⟨|Q0| + |Q1| + |Q2| + 1, by positivity, ?_⟩⟩
  · intro τ hτ i
    fin_cases i
    · refine le_trans (hP0 τ hτ) ?_
      linarith [le_abs_self P0, abs_nonneg P1, abs_nonneg P2]
    · refine le_trans (hP1 τ hτ) ?_
      linarith [le_abs_self P1, abs_nonneg P0, abs_nonneg P2]
    · refine le_trans (hP2 τ hτ) ?_
      linarith [le_abs_self P2, abs_nonneg P0, abs_nonneg P1]
  · intro z hz j
    fin_cases j
    · refine le_trans (hQ0 z hz) ?_
      linarith [le_abs_self Q0, abs_nonneg Q1, abs_nonneg Q2]
    · refine le_trans (hQ1 z hz) ?_
      linarith [le_abs_self Q1, abs_nonneg Q0, abs_nonneg Q2]
    · refine le_trans (hQ2 z hz) ?_
      linarith [le_abs_self Q2, abs_nonneg Q0, abs_nonneg Q1]

end Work.Asymptotics.MiddleRange
