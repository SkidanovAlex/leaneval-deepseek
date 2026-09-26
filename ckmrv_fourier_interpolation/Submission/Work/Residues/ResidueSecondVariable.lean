/-
# The residue of the kernels in the *second* variable (CKMRV (genpart5), the shift `T⁻¹`)

`Work.Residues.hasResidue_KPlus_T` and friends compute the residue of `τ ↦ K(τ,z)` at `τ = z+1`.
CKMRV Section 5.3 additionally needs the residue of the *other* variable,
`Res_{z = τ-1} K(τ,z) = 1/(2π)` (their `(genpart5)`: `Res_{τ=αz}(K|^z_{2-d/2}r) = -(j(α,z)^{d/2-2}/2π)φ(α ι(r))`,
read in the second variable, with `α = T⁻¹` and `r = 1`).  That is what this file proves, by the
same `Work.Residues.hasResidue_of_cleared` machine applied to the function
`ζ ↦ K(z,ζ)` (with `z` the fixed first argument): the cleared relation
`K^{Clear}(z,ζ) = Δ(z)Δ(ζ)^e (j(z)-j(ζ))K(z,ζ)` gives
`K(z,ζ)·(j ζ - j z) = -AfunPlus d ζ z`, and `AfunPlus d (z-1) z = -(1/(2π))j'(z)`.

Main results

* `Work.Residues.hasResidue_KPlus_second`, `hasResidue_KMinus_second` :
  `Res_{ζ = z-1} K_±(z,ζ) = 1/(2π)`;
* `Work.Residues.hasResidue_Kfun_second` : `Res_{ζ = z-1} K(z,ζ) = 1/(2π)`
  (the statement CKMRV Section 5.3 uses);
* `Work.Residues.hasResidue_Khat_second` : `Res_{ζ = z-1} K̂(z,ζ) = 0`;
* the `T⁻¹ • z` forms `hasResidue_KPlus_second'`, ... for callers who keep the group element.
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Kernels.KernelGrowth

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## Translating by `-1` -/

/-- `1 +ᵥ (-1 +ᵥ z) = z` on the upper half plane. -/
lemma one_vadd_neg_one_vadd (z : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z := by
  rw [← add_vadd, add_neg_cancel, zero_vadd]


lemma E4Fun_vadd_neg_one (z : ℍ) : E4Fun ((-1 : ℝ) +ᵥ z) = E4Fun z := by
  have h := KernelFacts.E4Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd z] at h
  exact h.symm

lemma E6Fun_vadd_neg_one (z : ℍ) : E6Fun ((-1 : ℝ) +ᵥ z) = E6Fun z := by
  have h := KernelFacts.E6Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd z] at h
  exact h.symm

lemma DeltaFun_vadd_neg_one (z : ℍ) : DeltaFun ((-1 : ℝ) +ᵥ z) = DeltaFun z := by
  have h := KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd z] at h
  exact h.symm

lemma jInvariantFun_vadd_neg_one (z : ℍ) :
    jInvariantFun ((-1 : ℝ) +ᵥ z) = jInvariantFun z := by
  have h := KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd z] at h
  exact h.symm

lemma jprime_vadd_neg_one (z : ℍ) : jprime ((-1 : ℝ) +ᵥ z) = jprime z := by
  simp only [jprime, E4Fun_vadd_neg_one, E6Fun_vadd_neg_one, DeltaFun_vadd_neg_one]

/-- `T⁻¹ • z = z - 1`. -/
lemma T_inv_smul_eq (z : ℍ) : ((ModularGroup.T⁻¹) • z : ℍ) = (-1 : ℝ) +ᵥ z := by
  simpa using (UpperHalfPlane.modular_T_zpow_smul z (-1 : ℤ))

/-! ## The cleared kernels in the second variable -/

/-- Holomorphy of `AfunPlus d · z` in the *first* variable (i.e. in the second variable of the
cleared kernel). -/
lemma mdifferentiableAt_AfunPlus_snd (d : ℕ) (hd : d = 8 ∨ d = 24) (z ζ₀ : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => AfunPlus d ζ z) ζ₀ := by
  have h1 : MDiff (fun ζ : ℍ => KPlusClear d z ζ) :=
    (KernelGrowth.KPlusClear_growth_z d hd z).1
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => DeltaFun z * DeltaFun ζ ^ dpow d) ζ₀ :=
    mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 ζ₀).pow _)
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact h1 ζ₀
  · exact h2
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ₀))

/-- Holomorphy of `AfunMinus ℓ d · z` in the first variable. -/
lemma mdifferentiableAt_AfunMinus_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z ζ₀ : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => AfunMinus ℓ d ζ z) ζ₀ := by
  have h1 : MDiff (fun ζ : ℍ => KMinusClear ℓ d z ζ) :=
    (KernelGrowth.KMinusClear_growth_z ℓ d hd z).1
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => DeltaFun z * DeltaFun ζ ^ dpow d) ζ₀ :=
    mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 ζ₀).pow _)
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact h1 ζ₀
  · exact h2
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ₀))

/-- The cleared identity in the second variable: for `ζ` with `j ζ ≠ j z`,
`K_+^{(d)}(z,ζ)·(j ζ - j z) = -AfunPlus d ζ z`. -/
lemma mul_slope_eq_AfunPlus_snd (d : ℕ) (hd : d = 8 ∨ d = 24) (z ζ : ℍ)
    (h : jInvariantFun ζ ≠ jInvariantFun z) :
    KPlus d z ζ * (jInvariantFun ζ - jInvariantFun z) = -AfunPlus d ζ z := by
  have hlink := ClearLink.KPlusClear_eq_smul d hd z ζ h.symm
  have hD : DeltaFun z * DeltaFun ζ ^ dpow d ≠ 0 :=
    mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ))
  rw [AfunPlus, ← neg_div, eq_div_iff]
  · rw [hlink]
    simp only [growthPrefactor, dpow]
    ring
  · exact hD

/-- The cleared identity in the second variable, for `K_-`. -/
lemma mul_slope_eq_AfunMinus_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z ζ : ℍ)
    (h : jInvariantFun ζ ≠ jInvariantFun z) :
    KMinus ℓ d z ζ * (jInvariantFun ζ - jInvariantFun z) = -AfunMinus ℓ d ζ z := by
  have hlink := ClearLink.KMinusClear_eq_smul ℓ d hd z ζ h.symm
  have hD : DeltaFun z * DeltaFun ζ ^ dpow d ≠ 0 :=
    mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ))
  rw [AfunMinus, ← neg_div, eq_div_iff]
  · rw [hlink]
    simp only [growthPrefactor, dpow]
    ring
  · exact hD

/-! ## The residues in the second variable -/

/-- **The residue of `K_+` in the second variable** (CKMRV (genpart5) with `α = T⁻¹`, `r = 1`):
for fixed `z`, the function `ζ ↦ K_+^{(d)}(z,ζ)` has residue `1/(2π)` at `ζ = z - 1`. -/
theorem hasResidue_KPlus_second (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => KPlus d z ζ) ((ModularGroup.T⁻¹) • z) (1 / (2 * Real.pi)) := by
  have hTz : jInvariantFun ((ModularGroup.T⁻¹) • z) = jInvariantFun z := by
    rw [T_inv_smul_eq]; exact jInvariantFun_vadd_neg_one z
  have hne' : jprime ((ModularGroup.T⁻¹) • z) ≠ 0 := by
    rw [T_inv_smul_eq]; rw [jprime_vadd_neg_one]; exact hne
  have hmain := hasResidue_of_cleared (f := fun ζ : ℍ => KPlus d z ζ)
    (A := fun ζ : ℍ => -AfunPlus d ζ z) (z := z) (z₀ := (ModularGroup.T⁻¹) • z)
    (c := jprime ((ModularGroup.T⁻¹) • z))
    ((mdifferentiableAt_AfunPlus_snd d hd z _).neg) hTz (tendsto_slope_jprime _) hne' ?_
  · have hA : AfunPlus d ((ModularGroup.T⁻¹) • z) z
        = -(1 / (2 * Real.pi)) * jprime ((ModularGroup.T⁻¹) • z) := by
      rw [T_inv_smul_eq]
      have h := AfunPlus_vadd_one_eq d hd ((-1 : ℝ) +ᵥ z)
      rw [one_vadd_neg_one_vadd z] at h
      rw [h, jprime_vadd_neg_one]
    have hval : -AfunPlus d ((ModularGroup.T⁻¹) • z) z / jprime ((ModularGroup.T⁻¹) • z)
        = 1 / (2 * Real.pi) := by
      rw [hA]
      field_simp
    rw [hval] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_slope_jprime ((ModularGroup.T⁻¹) • z)).eventually (eventually_ne_nhds hne')]
      with ζ hζ hζne
    have hslope : (jInvariantFun ζ - jInvariantFun ((ModularGroup.T⁻¹) • z)) /
        ((ζ : ℂ) - (((ModularGroup.T⁻¹) • z : ℍ) : ℂ)) ≠ 0 := hζne
    have hjnz : jInvariantFun ζ - jInvariantFun z ≠ 0 := by
      intro h0; exact hslope (by rw [hTz, h0, zero_div])
    exact mul_slope_eq_AfunPlus_snd d hd z ζ (sub_ne_zero.mp hjnz)

/-- **The residue of `K_-` in the second variable.** -/
theorem hasResidue_KMinus_second (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => KMinus ℓ d z ζ) ((ModularGroup.T⁻¹) • z)
      (1 / (2 * Real.pi)) := by
  have hTz : jInvariantFun ((ModularGroup.T⁻¹) • z) = jInvariantFun z := by
    rw [T_inv_smul_eq]; exact jInvariantFun_vadd_neg_one z
  have hne' : jprime ((ModularGroup.T⁻¹) • z) ≠ 0 := by
    rw [T_inv_smul_eq]; rw [jprime_vadd_neg_one]; exact hne
  have hmain := hasResidue_of_cleared (f := fun ζ : ℍ => KMinus ℓ d z ζ)
    (A := fun ζ : ℍ => -AfunMinus ℓ d ζ z) (z := z) (z₀ := (ModularGroup.T⁻¹) • z)
    (c := jprime ((ModularGroup.T⁻¹) • z))
    ((mdifferentiableAt_AfunMinus_snd ℓ d hd z _).neg) hTz (tendsto_slope_jprime _) hne' ?_
  · have hA : AfunMinus ℓ d ((ModularGroup.T⁻¹) • z) z
        = -(1 / (2 * Real.pi)) * jprime ((ModularGroup.T⁻¹) • z) := by
      rw [T_inv_smul_eq]
      have h := AfunMinus_vadd_one_eq ℓ d hd ((-1 : ℝ) +ᵥ z)
      rw [one_vadd_neg_one_vadd z] at h
      rw [h, jprime_vadd_neg_one]
    have hval : -AfunMinus ℓ d ((ModularGroup.T⁻¹) • z) z / jprime ((ModularGroup.T⁻¹) • z)
        = 1 / (2 * Real.pi) := by
      rw [hA]
      field_simp
    rw [hval] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin,
      (tendsto_slope_jprime ((ModularGroup.T⁻¹) • z)).eventually (eventually_ne_nhds hne')]
      with ζ hζ hζne
    have hslope : (jInvariantFun ζ - jInvariantFun ((ModularGroup.T⁻¹) • z)) /
        ((ζ : ℂ) - (((ModularGroup.T⁻¹) • z : ℍ) : ℂ)) ≠ 0 := hζne
    have hjnz : jInvariantFun ζ - jInvariantFun z ≠ 0 := by
      intro h0; exact hslope (by rw [hTz, h0, zero_div])
    exact mul_slope_eq_AfunMinus_snd ℓ d hd z ζ (sub_ne_zero.mp hjnz)

/-- The shifted form of `hasResidue_KPlus_second`: the pole is at `z - 1`. -/
theorem hasResidue_KPlus_second' (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => KPlus d z ζ) ((-1 : ℝ) +ᵥ z) (1 / (2 * Real.pi)) := by
  rw [← T_inv_smul_eq]; exact hasResidue_KPlus_second d hd z hne

/-- The shifted form of `hasResidue_KMinus_second`. -/
theorem hasResidue_KMinus_second' (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => KMinus ℓ d z ζ) ((-1 : ℝ) +ᵥ z) (1 / (2 * Real.pi)) := by
  rw [← T_inv_smul_eq]; exact hasResidue_KMinus_second ℓ d hd z hne

/-- **The residue of the kernel `K` in its second variable** (CKMRV Section 5.3):
for fixed `z` with `j'(z) ≠ 0`, the function `ζ ↦ K^{(d)}(z,ζ)` has residue `1/(2π)` at
`ζ = z - 1`.  This is the second-variable pole that the contour shift of CKMRV's proof of
Proposition 4.6 picks up. -/
theorem hasResidue_Kfun_second (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => Kfun ℓ d z ζ) ((ModularGroup.T⁻¹) • z)
      (1 / (2 * Real.pi)) := by
  have hp := (hasResidue_KPlus_second d hd z hne).const_mul (1 / 2 : ℂ)
  have hm := (hasResidue_KMinus_second ℓ d hd z hne).const_mul (1 / 2 : ℂ)
  have h := hp.add hm
  have hfun : (fun ζ : ℍ => Kfun ℓ d z ζ)
      = (fun ζ : ℍ => (1 / 2 : ℂ) * KPlus d z ζ)
        + (fun ζ : ℍ => (1 / 2 : ℂ) * KMinus ℓ d z ζ) := by
    funext ζ
    rw [Kfun_eq]
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  have hval : (1 / 2 : ℂ) * (1 / (2 * Real.pi)) + (1 / 2 : ℂ) * (1 / (2 * Real.pi))
      = 1 / (2 * Real.pi) := by ring
  rw [hval] at h
  exact h

/-- The shifted form of `hasResidue_Kfun_second`: `Res_{ζ = z-1} K(z,ζ) = 1/(2π)`. -/
theorem hasResidue_Kfun_second' (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => Kfun ℓ d z ζ) ((-1 : ℝ) +ᵥ z) (1 / (2 * Real.pi)) := by
  rw [← T_inv_smul_eq]; exact hasResidue_Kfun_second ℓ d hd z hne

/-- The residue of `K̂` in its second variable vanishes at `ζ = z - 1`. -/
theorem hasResidue_Khat_second (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun ζ : ℍ => Khat ℓ d z ζ) ((ModularGroup.T⁻¹) • z) 0 := by
  have hp := (hasResidue_KPlus_second d hd z hne).const_mul (1 / 2 : ℂ)
  have hm := (hasResidue_KMinus_second ℓ d hd z hne).const_mul (-(1 / 2) : ℂ)
  have h := hp.add hm
  have hfun : (fun ζ : ℍ => Khat ℓ d z ζ)
      = (fun ζ : ℍ => (1 / 2 : ℂ) * KPlus d z ζ)
        + (fun ζ : ℍ => (-(1 / 2) : ℂ) * KMinus ℓ d z ζ) := by
    funext ζ
    rw [Khat_eq]
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  have hval : (1 / 2 : ℂ) * (1 / (2 * Real.pi)) + (-(1 / 2) : ℂ) * (1 / (2 * Real.pi)) = 0 := by
    ring
  rw [hval] at h
  exact h

/-! ## The poles are genuine: the contour meets them at the shifted points

The converse of the containment theorem `Work.Residues.mdifferentiableAt_Kfun_snd`: since a
holomorphic function has residue `0`, a point at which the residue is `1/(2π) ≠ 0` is a genuine
pole.  In particular, for every `z` with `j'(z) ≠ 0` the point `z - 1` (on the translate
`T⁻¹` of the imaginary axis when `z` is) carries a pole of `ζ ↦ K(z,ζ)`: this is CKMRV's
statement that the pole at `z = T⁻¹τ` lies on the contour for `τ = 1 + it`, and hence that
`Work.Kernels.kernelTransform` takes the junk value `0` there. -/

/-- **`z - 1` is a genuine pole of `ζ ↦ K_+^{(d)}(z,ζ)`.** -/
theorem not_mdifferentiableAt_KPlus_second (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KPlus d z ζ) ((ModularGroup.T⁻¹) • z) := by
  intro hdiff
  have h0 : HasResidue (fun ζ : ℍ => KPlus d z ζ) ((ModularGroup.T⁻¹) • z) 0 :=
    hasResidue_of_mdifferentiableAt hdiff
  have h1 := hasResidue_KPlus_second d hd z hne
  have hC : (1 : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hC ((h0.unique h1).symm)

/-- **`z - 1` is a genuine pole of `ζ ↦ K_-^{(d)}(z,ζ)`.** -/
theorem not_mdifferentiableAt_KMinus_second (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) :
    ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KMinus ℓ d z ζ) ((ModularGroup.T⁻¹) • z) := by
  intro hdiff
  have h0 : HasResidue (fun ζ : ℍ => KMinus ℓ d z ζ) ((ModularGroup.T⁻¹) • z) 0 :=
    hasResidue_of_mdifferentiableAt hdiff
  have h1 := hasResidue_KMinus_second ℓ d hd z hne
  have hC : (1 : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hC ((h0.unique h1).symm)

/-- **`z - 1` is a genuine pole of `ζ ↦ K^{(d)}(z,ζ)`** (CKMRV's pole on the contour at
`τ = 1 + it`: take `z = 1 + it`, whose `T⁻¹`-translate is `it`). -/
theorem not_mdifferentiableAt_Kfun_second (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) :
    ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Kfun ℓ d z ζ) ((ModularGroup.T⁻¹) • z) := by
  intro hdiff
  have h0 : HasResidue (fun ζ : ℍ => Kfun ℓ d z ζ) ((ModularGroup.T⁻¹) • z) 0 :=
    hasResidue_of_mdifferentiableAt hdiff
  have h1 := hasResidue_Kfun_second ℓ d hd z hne
  have hC : (1 : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact hC ((h0.unique h1).symm)

end Work.Residues
