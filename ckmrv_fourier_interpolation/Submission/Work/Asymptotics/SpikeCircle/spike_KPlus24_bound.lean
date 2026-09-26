/-
# The spike-circle bound for `K_+^{(24)}`

`K_+^{(24)} = (π²/(36·1728·i·Δζ))·G24` (`Work.Residues.KPlus_twentyfour_eq`), and each of
the three groups of `G24` is a product of polynomially bounded atoms together with the
exponentially small coefficients `N0f, M0f, N2f, M2f` (`O(q)` each) resp. the square
`Qf² = (1728Δτ)²`.  Combining these in the weighted calculus `SBs` gives total exponent `0`.
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SBsAtoms
import Submission.Work.Asymptotics.SpikeCircle.SBs_KPlus24_coeffs
import Submission.Work.Residues.KPlus24Bound

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

set_option maxHeartbeats 2000000

open Work.Kernels

/-- The constant `-3i/π` of the `φ₀`-coefficients. -/
abbrev kpc : ℂ := -(3 : ℂ) * Complex.I / (Real.pi : ℂ)

/-- The `τ`-bracket `τ·N0f + (-3i/π)·M0f` of the `φ̃₀`-group of `G24`. -/
def kp24A0 (τ ζ : ℍ) : ℂ :=
  (τ : ℂ) * Work.Residues.KPlusAux.N0f (E2Fun τ) (E4Fun τ) (E6Fun τ)
      (Work.Residues.KPlusAux.kph τ ζ)
    + kpc * Work.Residues.KPlusAux.M0f (E2Fun τ) (E4Fun τ)
      (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)

/-- The `τ`-bracket `τ·N2f + (-3i/π)·M2f` of the `φ̃₂`-group of `G24`. -/
def kp24A2 (τ ζ : ℍ) : ℂ :=
  (τ : ℂ) * Work.Residues.KPlusAux.N2f (E2Fun τ) (E4Fun τ) (E6Fun τ)
      (Work.Residues.KPlusAux.kph τ ζ)
    + kpc * Work.Residues.KPlusAux.M2f (E2Fun τ) (E4Fun τ)
      (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)

/-- The `φ̃₀`-group of `G24`. -/
def kp24g0 (τ ζ : ℍ) : ℂ := phitVec ζ 0 * E4Fun ζ * kp24A0 τ ζ

/-- The `φ̃₁`-group of `G24`. -/
def kp24g1 (τ ζ : ℍ) : ℂ := phitVec ζ 1 * E14Fun ζ * (DeltaFun ζ)⁻¹ * ((-(2 : ℂ) / 1728)
    * (Work.Residues.KPlusAux.Qf (E4Fun τ) (E6Fun τ)) ^ 2
    * (Work.Residues.KPlusAux.kph τ ζ) * phi0 τ)

/-- The `φ̃₂`-group of `G24`. -/
def kp24g2 (τ ζ : ℍ) : ℂ := phitVec ζ 2 * kp24A2 τ ζ

/-- The prefactor `(36·1728·i·Δ(ζ))⁻¹` of `K_+^{(24)}`. -/
def kp24cd (_τ ζ : ℍ) : ℂ := (36 * 1728 * Complex.I * DeltaFun ζ)⁻¹

theorem SBs_kp24A0 {H : ℝ} (hH : 3 ≤ H) (hN0 : SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.N0f
    (E2Fun τ) (E4Fun τ) (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)))
    (hM0 : SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.M0f
    (E2Fun τ) (E4Fun τ) (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ))) :
    SBs H 2 kp24A0 :=
  SBs.of_pointwise
    (SBs.add ((SBs.mul (SBs_tau_at hH) hN0).mono (k' := 2) (by norm_num))
      (SBs.const_mul kpc hM0))
    (fun τ ζ _ _ _ => by rw [kp24A0])

theorem SBs_kp24A2 {H : ℝ} (hH : 3 ≤ H) (hN2 : SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.N2f
    (E2Fun τ) (E4Fun τ) (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ)))
    (hM2 : SBs H 2 (fun τ ζ => Work.Residues.KPlusAux.M2f
    (E2Fun τ) (E4Fun τ) (E6Fun τ) (Work.Residues.KPlusAux.kph τ ζ))) :
    SBs H 2 kp24A2 :=
  SBs.of_pointwise
    (SBs.add ((SBs.mul (SBs_tau_at hH) hN2).mono (k' := 2) (by norm_num))
      (SBs.const_mul kpc hM2))
    (fun τ ζ _ _ _ => by rw [kp24A2])

theorem SBs_kp24g0 {H : ℝ} (hH : 3 ≤ H) (hA : SBs H 2 kp24A0) : SBs H 2 kp24g0 :=
  SBs.of_pointwise ((SBs.mul (SBs.mul (SBs_phit0 hH) (SBs_E4_zeta hH)) hA).mono
    (k' := 2) (by norm_num)) (fun τ ζ _ _ _ => by rw [kp24g0])

theorem SBs_kp24g2 {H : ℝ} (hH : 3 ≤ H) (hA : SBs H 2 kp24A2) : SBs H 2 kp24g2 :=
  SBs.of_pointwise ((SBs.mul (SBs_phit2 hH) hA).mono (k' := 2) (by norm_num))
    (fun τ ζ _ _ _ => by rw [kp24g2])

theorem SBs_kp24g1 {H : ℝ} (hH : 3 ≤ H) : SBs H 2 kp24g1 := by
  have hH1 : (1 : ℝ) ≤ H := le_trans (by norm_num) hH
  have hQf2 : SBs H 4 (fun τ _ : ℍ =>
      (Work.Residues.KPlusAux.Qf (E4Fun τ) (E6Fun τ)) ^ 2) :=
    SBs.congr ((SBs.mul (SBs_Qf hH1) (SBs_Qf hH1)).mono (k' := 4) (by norm_num))
      (fun τ ζ => by ring)
  have hB : SBs H 4 (fun τ ζ : ℍ => (-(2 : ℂ) / 1728)
      * (Work.Residues.KPlusAux.Qf (E4Fun τ) (E6Fun τ)) ^ 2
      * (Work.Residues.KPlusAux.kph τ ζ) * phi0 τ) :=
    (SBs.mul (SBs.mul (SBs.const_mul (-(2 : ℂ) / 1728) hQf2) (SBs_kph hH))
      (SBs_phi0_tau hH)).mono (k' := 4) (by norm_num)
  have hP : SBs H 0 (fun τ ζ : ℍ => phitVec ζ 1 * E14Fun ζ) :=
    (SBs.mul (SBs_phit1 hH) (SBs_E14_zeta hH)).mono (k' := 0) (by norm_num)
  refine SBs.of_pointwise
    ((SBs.mul (SBs.mul hP (SBs_inv_Delta_zeta hH)) hB).mono (k' := 2) (by norm_num))
    (fun τ ζ _ _ _ => ?_)
  rw [kp24g1]

/-- `SBs`-bound for `G24`. -/
theorem SBs_G24 {H : ℝ} (hH : 3 ≤ H) (h0 : SBs H 2 kp24g0) (h1 : SBs H 2 kp24g1)
    (h2 : SBs H 2 kp24g2) : SBs H 2 (fun τ ζ => Work.Residues.G24 τ ζ) :=
  SBs.of_pointwise (SBs.add (SBs.add h0 h1) h2) (fun τ ζ _ _ _ => by
    rw [Work.Residues.G24, Work.Residues.g24P0, Work.Residues.g24P1, Work.Residues.g24P2,
      kp24g0, kp24g1, kp24g2, kp24A0, kp24A2, kpc, phi0, div_eq_mul_inv]
    ring)

/-- `SBs`-bound for the prefactor `(36·1728·i·Δ ζ)⁻¹`. -/
theorem SBs_kp24cd {H : ℝ} (hH : 3 ≤ H) : SBs H (-2) kp24cd := by
  refine SBs.congr (SBs.const_mul ((36 * 1728 * Complex.I)⁻¹) (SBs_inv_Delta_zeta hH))
    (fun τ ζ => ?_)
  rw [kp24cd]
  show (36 * 1728 * Complex.I)⁻¹ * (DeltaFun ζ)⁻¹ = (36 * 1728 * Complex.I * DeltaFun ζ)⁻¹
  simp only [mul_inv]

theorem SBs_KPlus24 : ∃ H : ℝ, SBs H 0 (fun τ ζ => KPlus 24 τ ζ) := by
  obtain ⟨H1, hN0, hM0, hN2, hM2⟩ := SBs_KPlus24_coeffs
  refine ⟨max 3 H1, ?_⟩
  have hH3 : 3 ≤ max 3 H1 := le_max_left _ _
  have hH1 : H1 ≤ max 3 H1 := le_max_right _ _
  have hA0 := SBs_kp24A0 hH3 (hN0.monoH hH1) (hM0.monoH hH1)
  have hA2 := SBs_kp24A2 hH3 (hN2.monoH hH1) (hM2.monoH hH1)
  refine SBs.of_pointwise
    ((SBs.mul (SBs.const_mul ((Real.pi : ℂ) ^ 2) (SBs_kp24cd hH3))
      (SBs_G24 hH3 (SBs_kp24g0 hH3 hA0) (SBs_kp24g1 hH3) (SBs_kp24g2 hH3 hA2))).mono
      (k' := 0) (by norm_num))
    (fun τ ζ hτ hζ _ => ?_)
  have hJ : Work.Residues.KPlusAux.kpJ τ ζ ≠ 0 := by
    simp only [Work.Residues.KPlusAux.kpJ, sub_ne_zero]
    exact jne_of_spike hτ hζ
  rw [Work.Residues.KPlus_twentyfour_eq τ ζ hJ, kp24cd, div_eq_mul_inv]

end Work.Asymptotics.SpikeCircle
