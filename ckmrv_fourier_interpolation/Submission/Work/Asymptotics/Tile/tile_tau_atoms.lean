import Mathlib
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2

namespace Work.Asymptotics.Tile

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

/-! ## Auxiliary lemmas for the translation `n +ᵥ w`, `n = ±1`

The atoms `E₄, E₆, E₈, E₁₀, Δ, ψ₂, ψ₄, Δ⁻¹, j` are evaluated at the `SL(2,ℤ)`-translates
`w ± 1` of a point `w` of the cusp-`0` tile `E = KEpsilon`.  Since `scale (w ± 1)` is
comparable to `scale w` and the `T`-periodic atoms do not change at all, every
`Bdd`-shape established at `w` transfers to `n +ᵥ w`. -/

/-- A `T`-periodic function is unchanged by the translation `n +ᵥ ·` for `n = ±1`. -/
private lemma vadd_eq_self_of_period (F : ℍ → ℂ) (hF : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) : F ((n : ℝ) +ᵥ w) = F w := by
  rcases hn with h | h
  · rw [h, Int.cast_one]; exact hF w
  · rw [h, Int.cast_neg, Int.cast_one]
    have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
    have h4 := hF ((-1 : ℝ) +ᵥ w)
    rw [h3] at h4
    exact h4.symm

private lemma norm_intCast_eq_one (n : ℤ) (hn : n = 1 ∨ n = -1) : ‖(n : ℂ)‖ = 1 := by
  rw [Complex.norm_intCast]
  rcases hn with h | h <;> rw [h] <;> norm_num

/-- The translation `n +ᵥ w` keeps `scale` comparable to `scale w` for `n = ±1`. -/
private lemma scale_vadd_int_le (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) :
    Work.Kernels.scale ((n : ℝ) +ᵥ w) ≤ 2 * Work.Kernels.scale w := by
  have hnorm : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
    rw [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast]
    calc ‖(n : ℂ) + (w : ℂ)‖ ≤ ‖(n : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖(w : ℂ)‖ := by rw [norm_intCast_eq_one n hn]
      _ = ‖(w : ℂ)‖ + 1 := by ring
  have him : ((n : ℝ) +ᵥ w).im = w.im := UpperHalfPlane.vadd_im _ _
  have hkey : Work.Kernels.scale ((n : ℝ) +ᵥ w)
      ≤ 1 + (w.im)⁻¹ + (‖(w : ℂ)‖ + 1) := by
    simp only [Work.Kernels.scale, him]
    linarith
  have h3 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  calc Work.Kernels.scale ((n : ℝ) +ᵥ w) ≤ 1 + (w.im)⁻¹ + (‖(w : ℂ)‖ + 1) := hkey
    _ = Work.Kernels.scale w + 1 := by simp only [Work.Kernels.scale]; ring
    _ ≤ 2 * Work.Kernels.scale w := by linarith

/-- Every member of `𝒫` (moderate growth on all of `ℍ`) is bounded by `C (scale w)^N` at
`n +ᵥ w`, uniformly for `n = ±1`. -/
private lemma exists_bound_vadd_of_moderate {F : ℍ → ℂ}
    (hF : Work.Kernels.ModerateGrowthOn Set.univ F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      ‖F ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨α, N, hα, hN, h⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ F).mp hF
  refine ⟨α * 2 ^ N + 1, N, ?_, hN, fun w n hn => ?_⟩
  · have : 0 < (2 : ℝ) ^ N := Real.rpow_pos_of_pos (by norm_num) N
    positivity
  · have h1 : ‖F ((n : ℝ) +ᵥ w)‖ ≤ α * (Work.Kernels.scale ((n : ℝ) +ᵥ w)) ^ N :=
      h ((n : ℝ) +ᵥ w) (Set.mem_univ _)
    have h2 : Work.Kernels.scale ((n : ℝ) +ᵥ w) ≤ 2 * Work.Kernels.scale w :=
      scale_vadd_int_le n hn w
    have hsp : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have h3 : (Work.Kernels.scale ((n : ℝ) +ᵥ w)) ^ N
        ≤ (2 * Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos _)) h2 hN
    have h4 : (2 * Work.Kernels.scale w) ^ N = 2 ^ N * (Work.Kernels.scale w) ^ N :=
      Real.mul_rpow (by norm_num) hsp.le
    have h5 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N := Real.rpow_nonneg hsp.le N
    calc ‖F ((n : ℝ) +ᵥ w)‖ ≤ α * (Work.Kernels.scale ((n : ℝ) +ᵥ w)) ^ N := h1
      _ ≤ α * (2 ^ N * (Work.Kernels.scale w) ^ N) :=
          mul_le_mul_of_nonneg_left (h4 ▸ h3) hα
      _ = α * 2 ^ N * (Work.Kernels.scale w) ^ N := by ring
      _ ≤ (α * 2 ^ N + 1) * (Work.Kernels.scale w) ^ N := by nlinarith [h5]

/-! ## The nine atoms at `n +ᵥ w` -/

private lemma exists_bound_E4 :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.E4Fun) Work.Kernels.ClassicalFacts.E4Fun_mem_InP.2
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_E6 :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.E6Fun) Work.Kernels.ClassicalFacts.E6Fun_mem_InP.2
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_E8 :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.E8Fun) (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.2.pow 2)
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_E10 :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.E10Fun)
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.2.mul
      Work.Kernels.ClassicalFacts.E6Fun_mem_InP.2)
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_Delta :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.DeltaFun) Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.2
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.psi2 ℓ) (Work.Asymptotics.psi_InP ℓ).1.2
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, h⟩ := exists_bound_vadd_of_moderate
    (F := Work.Kernels.psi4 ℓ) (Work.Asymptotics.psi_InP ℓ).2.2
  exact ⟨C, N, hC, hN, fun w n hn _ => h w n hn⟩

private lemma exists_bound_invDelta :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖(Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖
        ≤ C * (Work.Kernels.scale w) ^ N
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.EtailE.E_bdd_invDelta
  refine ⟨C, N, hC, hN, fun w n hn hw => ?_⟩
  have h := hb w hw
  rw [vadd_eq_self_of_period Work.Kernels.DeltaFun
    (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ) n hn w]
  exact h

private lemma exists_bound_j :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)‖
        ≤ C * (Work.Kernels.scale w) ^ N
            * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.EtailE.E_bdd_j
  refine ⟨C, N, hC, hN, fun w n hn hw => ?_⟩
  have h := hb w hw
  rw [vadd_eq_self_of_period Work.Kernels.jInvariantFun
    (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) n hn w]
  exact h

theorem tile_tau_atoms (ℓ : Work.Kernels.LogLambdaData) : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ‖Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖(Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖
          ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) ∧
        ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)‖
          ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
  obtain ⟨C4, N4, hC4, hN4, h4⟩ := exists_bound_E4
  obtain ⟨C6, N6, hC6, hN6, h6⟩ := exists_bound_E6
  obtain ⟨C8, N8, hC8, hN8, h8⟩ := exists_bound_E8
  obtain ⟨C10, N10, hC10, hN10, h10⟩ := exists_bound_E10
  obtain ⟨CD, ND, hCD, hND, hD⟩ := exists_bound_Delta
  obtain ⟨Cp2, Np2, hCp2, hNp2, hp2⟩ := exists_bound_psi2 ℓ
  obtain ⟨Cp4, Np4, hCp4, hNp4, hp4⟩ := exists_bound_psi4 ℓ
  obtain ⟨CiD, NiD, hCiD, hNiD, hiD⟩ := exists_bound_invDelta
  obtain ⟨Cj, Nj, hCj, hNj, hj⟩ := exists_bound_j
  refine ⟨C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1,
          N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro w n hn hw
    have hC4le : C4 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hC6le : C6 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hC8le : C8 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hC10le : C10 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hCDle : CD ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hCp2le : Cp2 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hCp4le : Cp4 ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hCiDle : CiD ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hCjle : Cj ≤ C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1 := by linarith
    have hN4le : N4 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hN6le : N6 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hN8le : N8 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hN10le : N10 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hNDle : ND ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hNp2le : Np2 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hNp4le : Np4 ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hNiDle : NiD ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    have hNjle : Nj ≤ N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc ‖Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)‖
          ≤ C4 * (Work.Kernels.scale w) ^ N4 := h4 w n hn hw
        _ ≤ C4 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hN4le) hC4.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hC4le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.E6Fun ((n : ℝ) +ᵥ w)‖
          ≤ C6 * (Work.Kernels.scale w) ^ N6 := h6 w n hn hw
        _ ≤ C6 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hN6le) hC6.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hC6le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)‖
          ≤ C8 * (Work.Kernels.scale w) ^ N8 := h8 w n hn hw
        _ ≤ C8 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hN8le) hC8.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hC8le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖
          ≤ C10 * (Work.Kernels.scale w) ^ N10 := h10 w n hn hw
        _ ≤ C10 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hN10le) hC10.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hC10le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖
          ≤ CD * (Work.Kernels.scale w) ^ ND := hD w n hn hw
        _ ≤ CD * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNDle) hCD.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hCDle
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w)‖
          ≤ Cp2 * (Work.Kernels.scale w) ^ Np2 := hp2 w n hn hw
        _ ≤ Cp2 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNp2le) hCp2.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hCp2le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)‖
          ≤ Cp4 * (Work.Kernels.scale w) ^ Np4 := hp4 w n hn hw
        _ ≤ Cp4 * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNp4le) hCp4.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj) :=
              mul_le_mul_of_nonneg_right hCp4le
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖(Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖
          ≤ CiD * (Work.Kernels.scale w) ^ NiD
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := hiD w n hn hw
        _ ≤ CiD * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj)
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNiDle) hCiD.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj)
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_right hCiDle
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · calc ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)‖
          ≤ Cj * (Work.Kernels.scale w) ^ Nj
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := hj w n hn hw
        _ ≤ Cj * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj)
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hNjle) hCj.le
        _ ≤ (C4 + C6 + C8 + C10 + CD + Cp2 + Cp4 + CiD + Cj + 1)
              * (Work.Kernels.scale w) ^ (N4 + N6 + N8 + N10 + ND + Np2 + Np4 + NiD + Nj)
              * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_right hCjle
                (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)

end

end Work.Asymptotics.Tile
