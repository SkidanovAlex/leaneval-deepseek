/-
# The numerator `Ξ_d` on the cusp-`±1` tile cone

This file proves `Work.Asymptotics.tileXi_poly`: for `w` in the cusp-`0` neighbourhood
`E = KEpsilon`, `n = ±1` and `z` with `1 ≤ Im z`, the cleared numerator `Ξ_d((n:ℝ)+ᵥw, z)`
(`d = 8, 24`) is bounded by `C (scale w)^N (1 + e^{2π(Im (S•w) - Im z)})`.

The `d = 8` case is proved in `Submission/Work/Asymptotics/TileCone/Xi8_tile_vadd_int.lean`
(via the cancelled form `Xi8_cancelled` and the cusp-`±1` atom inventory of
`Submission/Work/Asymptotics/tile_Bdd_atoms.lean` in the `Bdd` calculus of
`Submission/Work/Asymptotics/EtailE/Shapes.lean`).

The `d = 24` case is proved here by the same method: `Xi24_cancelled` writes `Ξ₂₄` as a sum of
products of a `τ`-factor and a `z`-factor; the `τ`-factors are `Bdd 0` (`E₄φ₈`, `φ₀E₄³`,
`τE₄²E₆`, `φ₂E₄E₆`, `φ₀Δ`) or `Bdd (2π)` (`E₄φ₈j`), and the `z`-factors at `1 ≤ Im z` are
bounded by constants or by `C‖q(z)‖` (`delta1_isBigOq`, `E2sq_minus_one`, `E4_minus_one`,
`jz_sigma_third`, `Xi24_z_bounds`, `DeltaFun_lower`).  The two exponentials combine into the
sharp factor `e^{2π(Im (S•w) - Im z)} = e^{2π Im (S•w)}·‖q(z)‖`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.TileCone.Basic
import Submission.Work.Asymptotics.TileCone.Xi8_tile_vadd_int
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.EtailE.Atoms

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Elementary helpers -/

/-- Monotonicity of the shape `C 𝓢^N E` in `C` and `N` (`𝓢 ≥ 1`). -/
private lemma shape_mono {𝓢 C N C' N' E : ℝ} (h𝓢 : 1 ≤ 𝓢) (hC : C ≤ C') (hN : N ≤ N')
    (hE : 0 ≤ E) (hC' : 0 ≤ C') : C * 𝓢 ^ N * E ≤ C' * 𝓢 ^ N' * E := by
  have h𝓢0 : (0 : ℝ) ≤ 𝓢 := le_trans zero_le_one h𝓢
  refine mul_le_mul_of_nonneg_right ?_ hE
  exact mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le h𝓢 hN) (Real.rpow_nonneg h𝓢0 N) hC'

/-- `‖q(z)‖ ≤ 1` at height `≥ 1`. -/
private lemma norm_qParam_le_one_im (z : ℍ) (hz : 1 ≤ z.im) : ‖qParamFun z‖ ≤ 1 := by
  rw [norm_qParamFun z, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz])

/-- Triangle inequality for the shape `‖(a - b) + c + d + e + g - h‖`. -/
private lemma norm_sum7_le (a b c d e g h : ℂ) :
    ‖(a - b) + c + d + e + g - h‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖g‖ + ‖h‖ := by
  have h1 := norm_sub_le ((a - b) + c + d + e + g) h
  have h2 := norm_add_le ((a - b) + c + d + e) g
  have h3 := norm_add_le ((a - b) + c + d) e
  have h4 := norm_add_le ((a - b) + c) d
  have h5 := norm_add_le (a - b) c
  have h6 := norm_sub_le a b
  linarith [h1, h2, h3, h4, h5, h6, norm_nonneg ((a - b) + c + d + e + g),
    norm_nonneg ((a - b) + c + d + e), norm_nonneg ((a - b) + c + d),
    norm_nonneg ((a - b) + c), norm_nonneg (a - b)]

/-- Absorption: from `A ≤ c·F·X`, `X ≤ 1 + E·Q`, `c ≤ Λ`, `F ≥ 0`, `E ≥ 1`, `Q ≥ 0`
conclude `A ≤ Λ·F·(1 + E·Q)`. -/
private lemma absorb {F E Q A c Λ X : ℝ} (hF : 0 ≤ F) (hE : 1 ≤ E) (hQ0 : 0 ≤ Q)
    (hA : A ≤ c * F * X) (hc : 0 ≤ c) (hX : X ≤ 1 + E * Q) (hcΛ : c ≤ Λ) :
    A ≤ Λ * F * (1 + E * Q) := by
  have h0 : 0 ≤ 1 + E * Q := by nlinarith [mul_nonneg (le_trans zero_le_one hE) hQ0]
  have h1 : 0 ≤ c * F := mul_nonneg hc hF
  have h2 : c * F * X ≤ c * F * (1 + E * Q) := mul_le_mul_of_nonneg_left hX h1
  have h3 : c * F * (1 + E * Q) ≤ Λ * F * (1 + E * Q) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcΛ hF) h0
  linarith

/-- Common shape for five `Bdd c`-functions. -/
private lemma bdd_fin5 {c : ℝ} {F1 F2 F3 F4 F5 : ℍ → ℂ}
    (h1 : EtailE.Bdd c F1) (h2 : EtailE.Bdd c F2) (h3 : EtailE.Bdd c F3)
    (h4 : EtailE.Bdd c F4) (h5 : EtailE.Bdd c F5) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : ℍ, w ∈ KEpsilon →
      (‖F1 w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
       ‖F2 w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
       ‖F3 w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
       ‖F4 w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im) ∧
       ‖F5 w‖ ≤ C * (scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)) := by
  obtain ⟨C1, N1, hC1, hN1, b1⟩ := h1
  obtain ⟨C2, N2, hC2, hN2, b2⟩ := h2
  obtain ⟨C3, N3, hC3, hN3, b3⟩ := h3
  obtain ⟨C4, N4, hC4, hN4, b4⟩ := h4
  obtain ⟨C5, N5, hC5, hN5, b5⟩ := h5
  refine ⟨C1 + C2 + C3 + C4 + C5, max N1 (max N2 (max N3 (max N4 N5))),
    by positivity, le_max_of_le_left hN1, fun w hw => ?_⟩
  have h𝓢 : (1 : ℝ) ≤ scale w := one_le_scale w
  have hE : (0 : ℝ) ≤ Real.exp (c * (ModularGroup.S • w).im) := Real.exp_nonneg _
  have hCc : (0 : ℝ) ≤ C1 + C2 + C3 + C4 + C5 := by positivity
  have hN2 : N2 ≤ max N1 (max N2 (max N3 (max N4 N5))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hN3 : N3 ≤ max N1 (max N2 (max N3 (max N4 N5))) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hN4 : N4 ≤ max N1 (max N2 (max N3 (max N4 N5))) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hN5 : N5 ≤ max N1 (max N2 (max N3 (max N4 N5))) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  refine ⟨le_trans (b1 w hw) (shape_mono h𝓢 (by linarith) (le_max_left _ _) hE hCc),
    le_trans (b2 w hw) (shape_mono h𝓢 (by linarith) hN2 hE hCc),
    le_trans (b3 w hw) (shape_mono h𝓢 (by linarith) hN3 hE hCc),
    le_trans (b4 w hw) (shape_mono h𝓢 (by linarith) hN4 hE hCc),
    le_trans (b5 w hw) (shape_mono h𝓢 (by linarith) hN5 hE hCc)⟩

/-- `Φ₈` is moderate on the cusp-`±1` tiles. -/
private lemma phi8_bdd_tile (n : ℤ) (hn : n = 1 ∨ n = -1) :
    EtailE.Bdd 0 (fun w : ℍ => phi8 ((n : ℝ) +ᵥ w)) := by
  have hτ : EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ)) := Bdd.vadd n hn
  have h4 : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E4 n hn
  have h6 : EtailE.Bdd 0 (fun w : ℍ => E6Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E6 n hn
  have h0 : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.congr (funext fun w => rfl) (Bdd.vadd_phi1 n hn)
  have h2 : EtailE.Bdd 0 (fun w : ℍ => phi2 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.congr (funext fun w => rfl) (Bdd.vadd_phi2 n hn)
  have hc2 : EtailE.Bdd 0 (fun w : ℍ => 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.congr (funext fun w => by ring)
      (EtailE.Bdd.const_mul 2 (EtailE.Bdd.mul_zero h0 h4))
  have hA : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w) *
      ((((n : ℝ) +ᵥ w : ℍ) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
        - 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    EtailE.Bdd.mul_zero h4 ((EtailE.Bdd.mul_zero hτ h6).sub hc2)
  have hB : EtailE.Bdd 0 (fun w : ℍ => E6Fun ((n : ℝ) +ᵥ w) * phi2 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mul_zero h6 h2
  exact EtailE.Bdd.congr (funext fun w => by simp only [phi8]) (hA.add hB)

/-! ## The `d = 24` bound on a fixed tile -/

private theorem xi24_tile_fixed (n : ℤ) (hn : n = 1 ∨ n = -1) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ KEpsilon → ∀ z : ℍ, 1 ≤ z.im →
        ‖Xi24 ((n : ℝ) +ᵥ w) z‖
          ≤ C * (scale w) ^ N
              * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  -- z-side inputs, at height `≥ 1`
  obtain ⟨Cσ, hCσ, hσz⟩ := delta1_isBigOq
  obtain ⟨Cq2, hCq2, hE2sq⟩ := E2sq_minus_one
  obtain ⟨Cq4, hCq4, hE4m1⟩ := E4_minus_one
  obtain ⟨Cj, hCj, hjzs⟩ := jz_sigma_third
  obtain ⟨CΔl, hCΔl, hΔl⟩ := DeltaFun_lower
  obtain ⟨Czb, hCzb, hzb⟩ := Xi24_z_bounds
  set KΔ : ℝ := Czb ^ 3 / CΔl with hKΔ
  have hKΔ0 : 0 ≤ KΔ := by rw [hKΔ]; positivity
  -- τ-side atoms
  have h4b : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E4 n hn
  have h6b : EtailE.Bdd 0 (fun w : ℍ => E6Fun ((n : ℝ) +ᵥ w)) := Bdd.vadd_E6 n hn
  have hDb : EtailE.Bdd 0 (fun w : ℍ => DeltaFun ((n : ℝ) +ᵥ w)) := Bdd.vadd_Delta n hn
  have hτb : EtailE.Bdd 0 (fun w : ℍ => (((n : ℝ) +ᵥ w : ℍ) : ℂ)) := Bdd.vadd n hn
  have h0b : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.congr (funext fun w => rfl) (Bdd.vadd_phi1 n hn)
  have h2b : EtailE.Bdd 0 (fun w : ℍ => phi2 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.congr (funext fun w => rfl) (Bdd.vadd_phi2 n hn)
  have h8b : EtailE.Bdd 0 (fun w : ℍ => phi8 ((n : ℝ) +ᵥ w)) := phi8_bdd_tile n hn
  have hjb : EtailE.Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun ((n : ℝ) +ᵥ w)) :=
    Bdd.shift EtailE.E_bdd_j (fun τ => KernelFacts.jInvariantFun_vadd_one τ) n hn
  -- the five `Bdd 0` τ-products
  have A2 : EtailE.Bdd 0 (fun w : ℍ => E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mul_zero h4b h8b
  have A3 : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3) := by
    refine EtailE.Bdd.congr (funext fun w => by ring)
      (EtailE.Bdd.mul_zero h0b ((EtailE.Bdd.mul_zero h4b h4b).mul_zero h4b))
  have A4 : EtailE.Bdd 0 (fun w : ℍ =>
      (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E4Fun ((n : ℝ) +ᵥ w) ^ 2 * E6Fun ((n : ℝ) +ᵥ w)) := by
    refine EtailE.Bdd.congr (funext fun w => by ring)
      ((EtailE.Bdd.mul_zero hτb (EtailE.Bdd.mul_zero h4b h4b)).mul_zero h6b)
  have A5 : EtailE.Bdd 0 (fun w : ℍ =>
      phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * E6Fun ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mul_zero (EtailE.Bdd.mul_zero h2b h4b) h6b
  have A6 : EtailE.Bdd 0 (fun w : ℍ => phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mul_zero h0b hDb
  have A1 : EtailE.Bdd (2 * Real.pi) (fun w : ℍ =>
      E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    EtailE.Bdd.mono (by linarith [Real.pi_pos])
      (EtailE.Bdd.mul (EtailE.Bdd.mul_zero h4b h8b) hjb)
  obtain ⟨C0, N0, hC0, hN0, hb0⟩ := bdd_fin5 A2 A3 A4 A5 A6
  obtain ⟨C1, N1, hC1, hN1, hb1⟩ := A1
  set Λ : ℝ := 6 * C1 * Cσ + 6 * C0 * (288 + Cj) + 1728 * C0 + 1728 * C0 * (5 * Cσ + 2 * Cq2)
      + 1728 * C0 * Cq2 + 1728 * C0 * Cq4 + 1728 * C0 * KΔ with hΛ
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  refine ⟨8 * Λ, max N0 N1, by positivity, le_max_of_le_left hN0, ?_⟩
  intro w hw z hz
  -- elementary facts
  have h𝓢 : (1 : ℝ) ≤ scale w := one_le_scale w
  have h𝓢0 : (0 : ℝ) ≤ scale w := le_trans zero_le_one h𝓢
  have hQ0 : (0 : ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hQ1 : ‖qParamFun z‖ ≤ 1 := norm_qParam_le_one_im z hz
  have hQpos : 0 < ‖qParamFun z‖ := by
    rw [norm_qParamFun z]
    exact Real.exp_pos _
  have hH2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have hH0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hH2
  set E : ℝ := Real.exp (2 * Real.pi * (ModularGroup.S • w).im) with hEdef
  have hE1 : 1 ≤ E := by
    rw [hEdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have hF : (0 : ℝ) ≤ (scale w) ^ (max N0 N1) := Real.rpow_nonneg h𝓢0 _
  have hGF : (scale w) ^ N0 ≤ (scale w) ^ (max N0 N1) :=
    Real.rpow_le_rpow_of_exponent_le h𝓢 (le_max_left _ _)
  have hHF : (scale w) ^ N1 ≤ (scale w) ^ (max N0 N1) :=
    Real.rpow_le_rpow_of_exponent_le h𝓢 (le_max_right _ _)
  have hGF0 : (0 : ℝ) ≤ (scale w) ^ N0 := Real.rpow_nonneg h𝓢0 N0
  have hHF0 : (0 : ℝ) ≤ (scale w) ^ N1 := Real.rpow_nonneg h𝓢0 N1
  -- the τ-atom shapes, in split form
  have hA1w : ‖E4Fun ((n : ℝ) +ᵥ w)‖ * ‖phi8 ((n : ℝ) +ᵥ w)‖
        * ‖jInvariantFun ((n : ℝ) +ᵥ w)‖ ≤ C1 * (scale w) ^ N1 * E := by
    have h := hb1 w hw
    rw [← hEdef] at h
    simpa only [norm_mul] using h
  have hA2w : ‖E4Fun ((n : ℝ) +ᵥ w)‖ * ‖phi8 ((n : ℝ) +ᵥ w)‖
      ≤ C0 * (scale w) ^ N0 := by
    have h := (hb0 w hw).1
    rw [EtailE.exp_zero_im w, mul_one] at h
    simpa only [norm_mul] using h
  have hA3w : ‖phi0 ((n : ℝ) +ᵥ w)‖ * ‖E4Fun ((n : ℝ) +ᵥ w) ^ 3‖
      ≤ C0 * (scale w) ^ N0 := by
    have h := (hb0 w hw).2.1
    rw [EtailE.exp_zero_im w, mul_one] at h
    simpa only [norm_mul] using h
  have hA4w : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ * ‖E4Fun ((n : ℝ) +ᵥ w) ^ 2‖
        * ‖E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C0 * (scale w) ^ N0 := by
    have h := (hb0 w hw).2.2.1
    rw [EtailE.exp_zero_im w, mul_one] at h
    simpa only [norm_mul] using h
  have hA5w : ‖phi2 ((n : ℝ) +ᵥ w)‖ * ‖E4Fun ((n : ℝ) +ᵥ w)‖
        * ‖E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C0 * (scale w) ^ N0 := by
    have h := (hb0 w hw).2.2.2.1
    rw [EtailE.exp_zero_im w, mul_one] at h
    simpa only [norm_mul] using h
  have hA6w : ‖phi0 ((n : ℝ) +ᵥ w)‖ * ‖DeltaFun ((n : ℝ) +ᵥ w)‖
      ≤ C0 * (scale w) ^ N0 := by
    have h := (hb0 w hw).2.2.2.2
    rw [EtailE.exp_zero_im w, mul_one] at h
    simpa only [norm_mul] using h
  -- the z-factors
  have hδz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * ‖qParamFun z‖ := by
    have h := hσz z hz
    simpa using h
  have hE2sqz : ‖E2Fun z ^ 2 - 1‖ ≤ Cq2 * ‖qParamFun z‖ := by
    have h := hE2sq z hz
    simpa using h
  have hE4m1z : ‖E4Fun z - 1‖ ≤ Cq4 * ‖qParamFun z‖ := by
    have h := hE4m1 z hz
    simpa using h
  have hjzσ : ‖jInvariantFun z‖ * ‖E4Fun z - E2Fun z ^ 2‖
      ≤ 288 + Cj * ‖qParamFun z‖ := by
    have h := hjzs z (by linarith : (1 / 3 : ℝ) ≤ z.im)
    have h288 : ‖(288 : ℂ)‖ = (288 : ℝ) := by norm_num
    calc ‖jInvariantFun z‖ * ‖E4Fun z - E2Fun z ^ 2‖
        = ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2)‖ := (norm_mul _ _).symm
      _ = ‖(jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288) + 288‖ := by ring_nf
      _ ≤ ‖jInvariantFun z * (E4Fun z - E2Fun z ^ 2) - 288‖ + ‖(288 : ℂ)‖ :=
            norm_add_le _ _
      _ ≤ Cj * ‖qParamFun z‖ + 288 := by rw [h288]; linarith
      _ = 288 + Cj * ‖qParamFun z‖ := by ring
  have hZ4 : ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
      ≤ (5 * Cσ + 2 * Cq2) * ‖qParamFun z‖ := by
    have h1 : ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ ≤ 5 * (Cσ * ‖qParamFun z‖) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hδz (by norm_num)
    have h2 : ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ ≤ 2 * (Cq2 * ‖qParamFun z‖) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hE2sqz (by norm_num)
    calc ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
        ≤ ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ + ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ :=
          norm_sub_le _ _
      _ ≤ 5 * (Cσ * ‖qParamFun z‖) + 2 * (Cq2 * ‖qParamFun z‖) := add_le_add h1 h2
      _ = (5 * Cσ + 2 * Cq2) * ‖qParamFun z‖ := by ring
  have hRRz : ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
      ≤ Czb * ‖qParamFun z‖ ^ 2 := (hzb z hz).2.1
  have hE4z : ‖E4Fun z‖ ≤ Czb := (hzb z hz).2.2.2.1
  have hΔzl : CΔl * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := hΔl z hz
  have hΔpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hCΔl hQpos) hΔzl
  -- the six terms of `Xi24_cancelled`
  let T1a : ℂ := 6 * (E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
      * jInvariantFun ((n : ℝ) +ᵥ w)) * (E4Fun z - E2Fun z ^ 2)
  let T1b : ℂ := 6 * (E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w))
      * (jInvariantFun z * (E4Fun z - E2Fun z ^ 2))
  let T1 : ℂ := 6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
      * (E4Fun z - E2Fun z ^ 2) * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)
  let T2 : ℂ := 1728 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
  let T3 : ℂ := 1728 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3
      * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
  let T4 : ℂ := 1728 * (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
      * E6Fun ((n : ℝ) +ᵥ w) * (E2Fun z ^ 2 - 1)
  let T5 : ℂ := 1728 * phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * E6Fun ((n : ℝ) +ᵥ w)
      * (E4Fun z - 1)
  let T6 : ℂ := 1728 * phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
      * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
      * E4Fun z ^ 2 / DeltaFun z
  have hT1eq : T1 = T1a - T1b := by
    dsimp only [T1, T1a, T1b]
    ring
  have hT1a : ‖T1a‖ ≤ 6 * (C1 * (scale w) ^ N1 * E) * (Cσ * ‖qParamFun z‖) := by
    dsimp only [T1a]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA1w (by norm_num)) hδz (norm_nonneg _)
      (by positivity)
  have hT1b : ‖T1b‖ ≤ 6 * (C0 * (scale w) ^ N0) * (288 + Cj * ‖qParamFun z‖) := by
    dsimp only [T1b]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA2w (by norm_num)) hjzσ (by positivity)
      (by positivity)
  have hT2 : ‖T2‖ ≤ 1728 * (C0 * (scale w) ^ N0) := by
    dsimp only [T2]
    rw [show (1728 : ℂ) * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
        = (1728 : ℂ) * (E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)) by ring]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hA2w (by norm_num)
  have hT3 : ‖T3‖ ≤ 1728 * (C0 * (scale w) ^ N0)
      * ((5 * Cσ + 2 * Cq2) * ‖qParamFun z‖) := by
    dsimp only [T3]
    rw [show (1728 : ℂ) * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
        = 1728 * (phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3)
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)) by ring]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA3w (by norm_num)) hZ4 (norm_nonneg _)
      (by positivity)
  have hT4 : ‖T4‖ ≤ 1728 * (C0 * (scale w) ^ N0) * (Cq2 * ‖qParamFun z‖) := by
    dsimp only [T4]
    rw [show (1728 : ℂ) * (((n : ℝ) +ᵥ w : ℍ) : ℂ) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
          * E6Fun ((n : ℝ) +ᵥ w) * (E2Fun z ^ 2 - 1)
        = 1728 * ((((n : ℝ) +ᵥ w : ℍ) : ℂ) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
          * E6Fun ((n : ℝ) +ᵥ w)) * (E2Fun z ^ 2 - 1) by ring]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA4w (by norm_num)) hE2sqz (norm_nonneg _)
      (by positivity)
  have hT5 : ‖T5‖ ≤ 1728 * (C0 * (scale w) ^ N0) * (Cq4 * ‖qParamFun z‖) := by
    dsimp only [T5]
    rw [show (1728 : ℂ) * phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
          * E6Fun ((n : ℝ) +ᵥ w) * (E4Fun z - 1)
        = 1728 * (phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
          * E6Fun ((n : ℝ) +ᵥ w)) * (E4Fun z - 1) by ring]
    simp only [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hA5w (by norm_num)) hE4m1z (norm_nonneg _)
      (by positivity)
  have hZa : ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
        * ‖E4Fun z ^ 2‖ ≤ (Czb * ‖qParamFun z‖ ^ 2) * Czb ^ 2 := by
    have h2 : ‖E4Fun z ^ 2‖ ≤ Czb ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4z 2
    exact mul_le_mul hRRz h2 (norm_nonneg _) (by positivity)
  have hT6 : ‖T6‖ ≤ 1728 * (C0 * (scale w) ^ N0) * KΔ := by
    dsimp only [T6]
    rw [show (1728 : ℂ) * phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z
        = 1728 * ((phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))
              * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
              * E4Fun z ^ 2) / DeltaFun z by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
    rw [norm_div]
    have hnum : ‖(1728 : ℂ) * ((phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2)‖
        ≤ 1728 * (C0 * (scale w) ^ N0) * ((Czb * ‖qParamFun z‖ ^ 2) * Czb ^ 2) := by
      have hsplit : ‖(1728 : ℂ) * ((phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2)‖
          = 1728 * (‖phi0 ((n : ℝ) +ᵥ w)‖ * ‖DeltaFun ((n : ℝ) +ᵥ w)‖)
              * (‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
                * ‖E4Fun z ^ 2‖) := by
        simp only [norm_mul, Complex.norm_ofNat]
        ring
      rw [hsplit]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hA6w (by norm_num)) hZa (by positivity)
        (by positivity)
    calc ‖(1728 : ℂ) * ((phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w))
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2)‖ / ‖DeltaFun z‖
        ≤ (1728 * (C0 * (scale w) ^ N0) * ((Czb * ‖qParamFun z‖ ^ 2) * Czb ^ 2))
            / (CΔl * ‖qParamFun z‖) :=
          div_le_div₀ (by positivity) hnum (mul_pos hCΔl hQpos) hΔzl
      _ = 1728 * C0 * KΔ * (scale w) ^ N0 * ‖qParamFun z‖ := by
          rw [hKΔ]
          field_simp
      _ ≤ 1728 * (C0 * (scale w) ^ N0) * (Czb ^ 3 / CΔl) := by
          have hQle : 1728 * C0 * (Czb ^ 3 / CΔl) * (scale w) ^ N0 * ‖qParamFun z‖
              ≤ 1728 * C0 * (Czb ^ 3 / CΔl) * (scale w) ^ N0 * 1 :=
            mul_le_mul_of_nonneg_left hQ1 (by positivity)
          calc 1728 * C0 * (Czb ^ 3 / CΔl) * (scale w) ^ N0 * ‖qParamFun z‖
              ≤ 1728 * C0 * (Czb ^ 3 / CΔl) * (scale w) ^ N0 * 1 := hQle
            _ = 1728 * (C0 * (scale w) ^ N0) * (Czb ^ 3 / CΔl) := by ring
  -- the triangle inequality
  have htri : ‖T1 + T2 + T3 + T4 + T5 - T6‖ ≤
      ‖T1a‖ + ‖T1b‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := by
    rw [hT1eq]
    exact norm_sum7_le T1a T1b T2 T3 T4 T5 T6
  -- absorption of each term
  have hb1a : ‖T1a‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 6 * C1 * Cσ) (X := E * ‖qParamFun z‖) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT1a ?_
      calc 6 * (C1 * (scale w) ^ N1 * E) * (Cσ * ‖qParamFun z‖)
          ≤ 6 * (C1 * (scale w) ^ (max N0 N1) * E) * (Cσ * ‖qParamFun z‖) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_right _ hE0
            exact mul_le_mul_of_nonneg_left hHF hC1.le
        _ = 6 * C1 * Cσ * (scale w) ^ (max N0 N1) * (E * ‖qParamFun z‖) := by ring
    · nlinarith only [mul_nonneg (le_trans zero_le_one hE1) hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h3 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h2, h3, h4, h5, h6]
  have hb1b : ‖T1b‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 6 * C0 * (288 + Cj)) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT1b ?_
      calc 6 * (C0 * (scale w) ^ N0) * (288 + Cj * ‖qParamFun z‖)
          ≤ 6 * (C0 * (scale w) ^ (max N0 N1)) * (288 + Cj) := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hGF hC0.le
            · have h := mul_le_mul_of_nonneg_left hQ1 hCj.le
              rw [mul_one] at h
              linarith
            · positivity
            · positivity
        _ = 6 * C0 * (288 + Cj) * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h3 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h3, h4, h5, h6]
  have hb2 : ‖T2‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 1728 * C0) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT2 ?_
      calc 1728 * (C0 * (scale w) ^ N0)
          ≤ 1728 * (C0 * (scale w) ^ (max N0 N1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGF hC0.le) (by norm_num)
        _ = 1728 * C0 * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h2, h4, h5, h6]
  have hb3 : ‖T3‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 1728 * C0 * (5 * Cσ + 2 * Cq2)) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT3 ?_
      calc 1728 * (C0 * (scale w) ^ N0) * ((5 * Cσ + 2 * Cq2) * ‖qParamFun z‖)
          ≤ 1728 * (C0 * (scale w) ^ (max N0 N1)) * (5 * Cσ + 2 * Cq2) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGF hC0.le)
                (by norm_num)
            · have h := mul_le_mul_of_nonneg_left hQ1 (by positivity : (0:ℝ) ≤ 5 * Cσ + 2 * Cq2)
              rwa [mul_one] at h
            · positivity
            · positivity
        _ = 1728 * C0 * (5 * Cσ + 2 * Cq2) * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h2, h4, h5, h6]
  have hb4 : ‖T4‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 1728 * C0 * Cq2) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT4 ?_
      calc 1728 * (C0 * (scale w) ^ N0) * (Cq2 * ‖qParamFun z‖)
          ≤ 1728 * (C0 * (scale w) ^ (max N0 N1)) * Cq2 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGF hC0.le)
                (by norm_num)
            · have h := mul_le_mul_of_nonneg_left hQ1 hCq2.le
              rwa [mul_one] at h
            · positivity
            · positivity
        _ = 1728 * C0 * Cq2 * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h3 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h2, h3, h5, h6]
  have hb5 : ‖T5‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 1728 * C0 * Cq4) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT5 ?_
      calc 1728 * (C0 * (scale w) ^ N0) * (Cq4 * ‖qParamFun z‖)
          ≤ 1728 * (C0 * (scale w) ^ (max N0 N1)) * Cq4 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGF hC0.le)
                (by norm_num)
            · have h := mul_le_mul_of_nonneg_left hQ1 hCq4.le
              rwa [mul_one] at h
            · positivity
            · positivity
        _ = 1728 * C0 * Cq4 * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h3 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h6 : (0 : ℝ) ≤ 1728 * C0 * KΔ := by positivity
      linarith only [h0, h1, h2, h3, h4, h6]
  have hb6 : ‖T6‖ ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    refine absorb (c := 1728 * C0 * KΔ) (X := 1) hF hE1 hQ0 ?_ (by positivity) ?_ ?_
    · refine le_trans hT6 ?_
      calc 1728 * (C0 * (scale w) ^ N0) * KΔ
          ≤ 1728 * (C0 * (scale w) ^ (max N0 N1)) * KΔ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGF hC0.le) (by norm_num))
              (by positivity)
        _ = 1728 * C0 * KΔ * (scale w) ^ (max N0 N1) * 1 := by ring
    · nlinarith only [hE1, hQ0]
    · rw [hΛ]
      have h0 : (0 : ℝ) ≤ 6 * C1 * Cσ := by positivity
      have h1 : (0 : ℝ) ≤ 6 * C0 * (288 + Cj) := by positivity
      have h2 : (0 : ℝ) ≤ 1728 * C0 := by positivity
      have h3 : (0 : ℝ) ≤ 1728 * C0 * (5 * Cσ + 2 * Cq2) := by positivity
      have h4 : (0 : ℝ) ≤ 1728 * C0 * Cq2 := by positivity
      have h5 : (0 : ℝ) ≤ 1728 * C0 * Cq4 := by positivity
      linarith only [h0, h1, h2, h3, h4, h5]
  have hsum : ‖T1a‖ + ‖T1b‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖
      ≤ 8 * Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
    have hΛF : (0 : ℝ) ≤ Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := by
      have h1 : (0 : ℝ) ≤ 1 + E * ‖qParamFun z‖ := by nlinarith only [hE1, hQ0]
      positivity
    linarith only [hb1a, hb1b, hb2, hb3, hb4, hb5, hb6, hΛF]
  -- conclusion
  have hexpq : E * ‖qParamFun z‖
      = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := by
    rw [hEdef, norm_qParamFun z, ← Real.exp_add]
    congr 1
    ring
  rw [Xi24_cancelled ((n : ℝ) +ᵥ w) z (ClassicalFacts.DeltaFun_ne_zero _)
    (ClassicalFacts.DeltaFun_ne_zero _)]
  show ‖T1 + T2 + T3 + T4 + T5 - T6‖ ≤ 8 * Λ * (scale w) ^ (max N0 N1)
      * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)))
  calc ‖T1 + T2 + T3 + T4 + T5 - T6‖
      ≤ ‖T1a‖ + ‖T1b‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ + ‖T6‖ := htri
    _ ≤ 8 * Λ * (scale w) ^ (max N0 N1) * (1 + E * ‖qParamFun z‖) := hsum
    _ = 8 * Λ * (scale w) ^ (max N0 N1)
          * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by rw [hexpq]

/-- The `d = 24` bound, for both tiles. -/
private theorem xi24_tile_vadd_int :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ z : ℍ, 1 ≤ z.im →
        ‖Xi24 ((n : ℝ) +ᵥ w) z‖
          ≤ C * (scale w) ^ N
              * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := xi24_tile_fixed 1 (Or.inl rfl)
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := xi24_tile_fixed (-1) (Or.inr rfl)
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn z hz
  have h𝓢 : (1 : ℝ) ≤ scale w := one_le_scale w
  have h𝓢0 : (0 : ℝ) ≤ scale w := le_trans zero_le_one h𝓢
  have hE : (0 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)) := by
    positivity
  have hC12 : (0 : ℝ) ≤ C1 + C2 := by linarith
  have step1 : C1 * (scale w) ^ N1 ≤ (C1 + C2) * (scale w) ^ (max N1 N2) :=
    mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le h𝓢 (le_max_left N1 N2))
      (Real.rpow_nonneg h𝓢0 N1) hC12
  have step2 : C2 * (scale w) ^ N2 ≤ (C1 + C2) * (scale w) ^ (max N1 N2) :=
    mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le h𝓢 (le_max_right N1 N2))
      (Real.rpow_nonneg h𝓢0 N2) hC12
  rcases hn with h | h
  · subst h
    exact le_trans (h1 w hw z hz) (mul_le_mul_of_nonneg_right step1 hE)
  · subst h
    exact le_trans (h2 w hw z hz) (mul_le_mul_of_nonneg_right step2 hE)

/-! ## The numerator `Ξ_d` on the cusp-`±1` tile cone -/

/-- **The numerator `Ξ_d` on the cusp-`±1` tile cone.**

For `w ∈ E = KEpsilon`, `n = ±1` and `z` in the cone `{z : 1 ≤ Im z}`, the `K_+`-cleared
numerator `Ξ_d((n:ℝ)+ᵥw, z)` (`Work.Asymptotics.Xi8` for `d = 8`, `Work.Asymptotics.Xi24` for
`d = 24`) is bounded by `scale w` to a power times `1 + e^{2π(Im (S•w) - Im z)}`, with the
*sharp* rate `2π` **in the own height `Im z`** (this is the rate at which the divisor
`Δ(z)(jτ - jz)` grows in `Work.Asymptotics.tile_divisor_lower_cone`, so the two cancel).

It is an input of the cone-separated bound
`Work.Asymptotics.offspike_bound_general` (`Submission/Work/Asymptotics/TileCone/OffSpike.lean`),
which is the off-spike half of `Work.Asymptotics.tilePPWindow_lowHalf`.

Numerical verification (validated model `_zz_klib.py`, `w = i·0.02`, `d = 8, 24`, `Im z` from `1`
to `100`): the ratio `‖Ξ_d(τ,z)‖ · e^{-2π(Im (S•w) - Im z)}` is *constant* in `Im z` over
`Im z ≤ Im (S•w)` (≈ `2.3·10^7` for `d = 8`, ≈ `1.5·10^24` for `d = 24`), i.e. the rate is
saturated.  Note this is **not** a corollary of `Xi8_bound_E`/`Xi24_bound_E`: those need
`Im (S • τ) ≥ 3/2`, whereas `S • (n+w)` has imaginary part `≈ Im w → 0` on the tile.

Route: expand `Xi8 τ z` by `Xi8_expand` (and `Xi24` analogously; both expansions are already
proved in the workspace).  Every term is of the form `f(τ)·g(z)` with
* `f(τ)` a sum of products of the tile atoms `τ, E₂, E₄, E₆` and `E₁₄/Δ` at `τ = n+w`, each
  bounded by a power of `scale w` via the S-laws `E₂(τ) = τ²E₂(Sτ) - 6iτ/π`,
  `E₄(τ) = τ⁴E₄(Sτ)`, `E₆(τ) = τ⁶E₆(Sτ)`, `Δ(τ) = τ¹²Δ(Sτ)` (all in
  `Submission/Work/Asymptotics/Xi8_bound_E.lean`) and the funnel bounds at `S w`;
* `g(z)` either the pair `Δ(z)(jτ - jz)` (bounded by `C(1+e^{2π(A-Im z)})` with `A = Im (S•w)`,
  using `Δ(z)(jτ-jz) = Δ(z)j(w) - E₄(z)³`, `‖Δ(z)‖ ≤ 2e^{-2π Im z}` and `‖j(w)‖ ≤ 3e^{2πA}`) or a
  product of `E₂(z), E₄(z), E₆(z), Δ(z)` at height `Im z ≥ 1`, all bounded by absolute constants
  (`cfx_E4_third_order`, `cfx_E6_third_order`, `cfx_Delta_third_order`, `E2Fun_bound`). -/
theorem tileXi_poly (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        ‖(if d = 8 then Work.Asymptotics.Xi8 ((n : ℝ) +ᵥ w) z
            else Work.Asymptotics.Xi24 ((n : ℝ) +ᵥ w) z)‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im))) := by
  rcases hd with hd8 | hd24
  · obtain ⟨C, N, hC, hN, h⟩ := TileCone.Xi8_tile_vadd_int
    exact ⟨C, N, hC, hN, fun w hw n hn z hz => by simpa [hd8] using h w hw n hn z hz⟩
  · obtain ⟨C, N, hC, hN, h⟩ := xi24_tile_vadd_int
    exact ⟨C, N, hC, hN, fun w hw n hn z hz => by simpa [hd24] using h w hw n hn z hz⟩

end

end Work.Asymptotics
