/-
# The residue theorem of CKMRV Theorem 4.9(3) for `K_-`

This is the `K_-` companion of `Work.Residues.ResidueTheorem`.  The kernel `K_-^{(d)}` is
annihilated by `𝓘_- = (S-I)R + (T-I)²R + (z-1)R`, so its residue functional factors through
the three-dimensional quotient `R/𝓘_-` with basis `1, T, TS`; the residues at the poles
`z`, `Tz`, `TS·z` are `-(1/2π)φ_-(1) = 0`, `-(1/2π)φ_-(T) = -1/(2π)` and
`-(1/2π)φ_-(TS) = 0`.

## Main results

* `Work.Residues.KMinus_slash_eq_zero_of_mem_idealIm` : `K_- |^τ r = 0` for `r ∈ 𝓘_-`.
* `Work.Residues.hasResidue_KMinus_self`, `hasResidue_KMinus_T`, `hasResidue_KMinus_TS`.
* `Work.Residues.hasResidue_slash_KMinus` : the residue theorem for `K_-`.
-/
import Mathlib
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## The cleared kernel `K_-` divided by `Δ(τ)Δ(z)^e` -/

/-- The cleared kernel `K_-` divided by its `τ`-dependent denominator. -/
def AfunMinus (ℓ : LogLambdaData) (d : ℕ) (z : ℍ) (τ : ℍ) : ℂ :=
  KMinusClear ℓ d τ z / (DeltaFun τ * DeltaFun z ^ dpow d)

lemma mdifferentiableAt_AfunMinus (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (τ₀ : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (AfunMinus ℓ d z) τ₀ := by
  have h1 : MDiff (fun τ : ℍ => KMinusClear ℓ d τ z) :=
    (KernelGrowth.KMinusClear_growth_tau ℓ d hd z).1
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => DeltaFun τ * DeltaFun z ^ dpow d) τ₀ :=
    (ClassicalFacts.DeltaFun_mem_InP.1 τ₀).mul mdifferentiableAt_const
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact h1 τ₀
  · exact h2
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ₀)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

lemma mul_slope_eq_AfunMinus (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z τ : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun z) :
    KMinus ℓ d τ z * (jInvariantFun τ - jInvariantFun z) = AfunMinus ℓ d z τ := by
  have hlink := ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  rw [AfunMinus, eq_div_iff]
  · rw [hlink]
    simp only [growthPrefactor, dpow]
    ring
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

/-- `AfunMinus` at `τ = Tz` equals `iE₄²E₆/Δ(z)`. -/
lemma AfunMinus_vadd_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunMinus ℓ d z ((1 : ℝ) +ᵥ z) =
      Complex.I * E4Fun z ^ 2 * E6Fun z / DeltaFun z := by
  have hD1 : DeltaFun ((1 : ℝ) +ᵥ z) = DeltaFun z := KernelFacts.DeltaFun_vadd_one z
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [AfunMinus, KMinusClear_T ℓ d hd z, hD1]
  simp only [dpow]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero hD (pow_ne_zero _ hD))]

/-- `AfunMinus` at `τ = Tz` equals `-(1/2π)·j'(Tz)`. -/
lemma AfunMinus_vadd_one_eq (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunMinus ℓ d z ((1 : ℝ) +ᵥ z) = -(1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ z) := by
  rw [AfunMinus_vadd_one ℓ d hd z, jprime_vadd_one, jprime]
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-! ## The residue of `K_-` at the three points of the orbit -/

/-- The residue of `K_-^{(d)}(·,z)` at `τ = z` is `0 = -(1/2π)φ_-(1)`. -/
theorem hasResidue_KMinus_self (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) : HasResidue (fun τ : ℍ => KMinus ℓ d τ z) z 0 := by
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KMinus ℓ d τ z) (A := AfunMinus ℓ d z)
    (z₀ := z) (z := z) (c := jprime z)
    (mdifferentiableAt_AfunMinus ℓ d hd z z) rfl (tendsto_slope_jprime z) hne ?_
  · have h : AfunMinus ℓ d z z = 0 := by
      simp only [AfunMinus, KMinusClear_diag ℓ d hd z, zero_div]
    rw [h, zero_div] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime z).eventually
      (eventually_ne_nhds hne)] with τ hτ hτne
    have hslope : (jInvariantFun τ - jInvariantFun z) / ((τ : ℂ) - (z : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    exact mul_slope_eq_AfunMinus ℓ d hd z τ (sub_ne_zero.mp hjnz)

/-- The residue of `K_-^{(d)}(·,z)` at `τ = Tz = z+1` is `-(1/2π)φ_-(T) = -1/(2π)`. -/
theorem hasResidue_KMinus_T (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KMinus ℓ d τ z) ((1 : ℝ) +ᵥ z) (-(1 / (2 * Real.pi))) := by
  have hT : jInvariantFun ((1 : ℝ) +ᵥ z) = jInvariantFun z :=
    KernelFacts.jInvariantFun_vadd_one z
  have hneT : jprime ((1 : ℝ) +ᵥ z) ≠ 0 := by
    rw [jprime_ne_zero_iff] at hne ⊢
    rwa [KernelFacts.E4Fun_vadd_one, KernelFacts.E6Fun_vadd_one]
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KMinus ℓ d τ z) (A := AfunMinus ℓ d z)
    (z₀ := (1 : ℝ) +ᵥ z) (z := z) (c := jprime ((1 : ℝ) +ᵥ z))
    (mdifferentiableAt_AfunMinus ℓ d hd z _) hT (tendsto_slope_jprime _) hneT ?_
  · have hcancel : -(1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ z) / jprime ((1 : ℝ) +ᵥ z)
        = -(1 / (2 * Real.pi)) := by
      rw [mul_div_assoc, div_self hneT, mul_one]
    rw [AfunMinus_vadd_one_eq ℓ d hd z, hcancel] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime _).eventually
      (eventually_ne_nhds hneT)] with τ hτ hτne
    have hslope : (jInvariantFun τ - jInvariantFun ((1 : ℝ) +ᵥ z)) /
        ((τ : ℂ) - (((1 : ℝ) +ᵥ z : ℍ) : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun ((1 : ℝ) +ᵥ z) ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hjnz' : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      have hh := hjnz
      rw [hT] at hh
      exact hh
    exact mul_slope_eq_AfunMinus ℓ d hd z τ (sub_ne_zero.mp hjnz')

/-- The residue of `K_-^{(d)}(·,z)` at `τ = TS·z` is `0 = -(1/2π)φ_-(TS)`. -/
theorem hasResidue_KMinus_TS (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KMinus ℓ d τ z) ((ModularGroup.T * ModularGroup.S) • z) 0 := by
  have hTS : (ModularGroup.T * ModularGroup.S) • z = (1 : ℝ) +ᵥ (ModularGroup.S • z) :=
    T_mul_S_smul z
  have hj : jInvariantFun ((ModularGroup.T * ModularGroup.S) • z) = jInvariantFun z := by
    rw [hTS, KernelFacts.jInvariantFun_vadd_one, KernelFacts.jInvariantFun_S_smul]
  have hne' : jprime ((ModularGroup.T * ModularGroup.S) • z) ≠ 0 := by
    rw [hTS, jprime_vadd_one]
    rw [jprime_ne_zero_iff] at hne ⊢
    rw [E4Fun_S_smul, E6Fun_S_smul]
    have hz : (z : ℂ) ≠ 0 := by exact_mod_cast z.ne_zero
    rw [mul_ne_zero_iff] at hne
    rw [mul_ne_zero_iff]
    exact ⟨mul_ne_zero (pow_ne_zero _ hz) hne.1, mul_ne_zero (pow_ne_zero _ hz) hne.2⟩
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KMinus ℓ d τ z) (A := AfunMinus ℓ d z)
    (z₀ := (ModularGroup.T * ModularGroup.S) • z) (z := z) (c := jprime _)
    (mdifferentiableAt_AfunMinus ℓ d hd z _) hj (tendsto_slope_jprime _) hne' ?_
  · have hA0 : AfunMinus ℓ d z ((ModularGroup.T * ModularGroup.S) • z) = 0 := by
      rw [hTS, AfunMinus, KMinusClear_TS ℓ d hd z, zero_div]
    rw [hA0, zero_div] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime _).eventually
      (eventually_ne_nhds hne')] with τ hτ hτne
    have hslope : (jInvariantFun τ - jInvariantFun ((ModularGroup.T * ModularGroup.S) • z)) /
        ((τ : ℂ) - (((ModularGroup.T * ModularGroup.S) • z : ℍ) : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun ((ModularGroup.T * ModularGroup.S) • z) ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hjnz' : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      have hh := hjnz
      rw [hj] at hh
      exact hh
    exact mul_slope_eq_AfunMinus ℓ d hd z τ (sub_ne_zero.mp hjnz')

/-! ## `K_-` is annihilated by `𝓘_-` -/

lemma KMinus_slash_eq_zero_of_mem_idealIm (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) {x : R} (hx : x ∈ idealIm) :
    slash ((d : ℤ) / 2) x (fun σ : ℍ => KMinus ℓ d σ z) = 0 := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p, q, hp⟩ := mem_span2.mp ha
  rw [hp, slash_add, slash_add, AlgebraFacts.slash_mul, AlgebraFacts.slash_mul,
    KMinus_slash_S_sub ℓ d hd z, KMinus_slash_T2 ℓ d hd z,
    AlgebraFacts.slash_mul_aux_zero, AlgebraFacts.slash_mul_aux_zero,
    slash_mem_augIdeal (even_div_two d hd) hc, add_zero, add_zero]

/-! ## The residue theorem for `K_-` -/

/-- The residue of the `r = 1` slashed kernel `K_-` at `τ = z` is `0 = -(1/2π)φ_-(1)`. -/
theorem hasResidue_slash_KMinus_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) 1 (fun σ : ℍ => KMinus ℓ d σ z)) z 0 := by
  have h : slash ((d : ℤ) / 2) (1 : R) (fun σ : ℍ => KMinus ℓ d σ z)
      = fun τ : ℍ => KMinus ℓ d τ z := by
    funext τ
    rw [slash_one]
  rw [h]
  exact hasResidue_KMinus_self ℓ d hd z hne

/-- The residue of the `r = T` slashed kernel `K_-` at `τ = z` is `-1/(2π) = -(1/2π)φ_-(T)`. -/
theorem hasResidue_slash_KMinus_T (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) R_T (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi))) := by
  have hres := hasResidue_KMinus_T ℓ d hd z hne
  rw [show (1 : ℝ) +ᵥ z = ModularGroup.T • z by
    simpa using (UpperHalfPlane.modular_T_zpow_smul z (1 : ℤ)).symm] at hres
  have h := hasResidue_smul_SL (f := fun σ : ℍ => KMinus ℓ d σ z)
    (z := z) (c := -(1 / (2 * Real.pi))) ModularGroup.T ((d : ℤ) / 2) hres
  have hj : (jFun ModularGroup.T (z : ℂ)) ^ (2 - (d : ℤ) / 2) = 1 := by
    have h1 : jFun ModularGroup.T (z : ℂ) = 1 := by
      rw [jFun_apply]
      have hcoe : ((ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by decide
      have hcoe' : ((ModularGroup.T : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by decide
      rw [hcoe, hcoe']; ring
    rw [h1, _root_.one_zpow]
  rw [hj, one_mul] at h
  have hfun : (fun τ : ℍ => (jFun ModularGroup.T (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
      (fun σ : ℍ => KMinus ℓ d σ z) (ModularGroup.T • τ))
      = (fun τ : ℍ => slash ((d : ℤ) / 2) R_T (fun σ : ℍ => KMinus ℓ d σ z) τ) := by
    funext τ
    rw [slash_R_T_eq]
  rwa [hfun] at h

/-- The residue of the `r = TS` slashed kernel `K_-` at `τ = z` is `0 = -(1/2π)φ_-(TS)`. -/
theorem hasResidue_slash_KMinus_TS (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (slash ((d : ℤ) / 2) (R_T * R_S) (fun σ : ℍ => KMinus ℓ d σ z)) z 0 := by
  have h := hasResidue_smul_SL (f := fun σ : ℍ => KMinus ℓ d σ z)
    (z := z) (c := 0) (ModularGroup.T * ModularGroup.S) ((d : ℤ) / 2)
    (hasResidue_KMinus_TS ℓ d hd z hne)
  rw [mul_zero] at h
  have hf : slash ((d : ℤ) / 2) (R_T * R_S) (fun σ : ℍ => KMinus ℓ d σ z)
      = fun τ : ℍ => (jFun (ModularGroup.T * ModularGroup.S) (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
          (fun σ : ℍ => KMinus ℓ d σ z) ((ModularGroup.T * ModularGroup.S) • τ) := by
    funext τ
    rw [slash_mul_T_S]
  rw [hf]
  exact h

/-- **Theorem 4.9(3) for `K_-`.**  For every `r : R` and every `z` with `j'(z) ≠ 0`, the
function `τ ↦ (K_-^{(d)} |^τ_{d/2} r)(τ,z)` has at `τ = z` at most a simple pole, with
residue `-(1/2π)·φ_-(r)`. -/
theorem hasResidue_slash_KMinus (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (r : R) :
    HasResidue (slash ((d : ℤ) / 2) r (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phiMinus r) := by
  obtain ⟨c, hc⟩ := exists_sub_sum_smul_M3_mem_idealIm r
  have hexp : (∑ i : Fin 3, c i • M3 i) = c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S) := by
    rw [Fin.sum_univ_three, M3_zero, M3_one, M3_two]
  have hφ : phiMinus r = phiMinus (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S)) := by
    have h0 : phiMinus (r - ∑ i : Fin 3, c i • M3 i) = 0 :=
      phiMinus_eq_zero_of_mem_idealIm hc
    have hsr : r = (r - ∑ i : Fin 3, c i • M3 i) + ∑ i : Fin 3, c i • M3 i := by abel
    rw [hsr, map_add, h0, zero_add, hexp]
  have h0 : HasResidue (slash ((d : ℤ) / 2) (r - ∑ i : Fin 3, c i • M3 i)
      (fun σ : ℍ => KMinus ℓ d σ z)) z 0 := by
    rw [KMinus_slash_eq_zero_of_mem_idealIm ℓ d hd z hc, HasResidue]
    simpa using tendsto_const_nhds (x := (0 : ℂ))
  have t0 : HasResidue (slash ((d : ℤ) / 2) (c 0 • (1 : R)) (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phiMinus (c 0 • (1 : R))) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiMinus_one, smul_zero, mul_zero]
    have h := (hasResidue_slash_KMinus_one ℓ d hd z hne).const_mul (c 0)
    rw [mul_zero] at h
    convert h using 1
    all_goals (ext τ; rw [Pi.smul_apply, smul_eq_mul])
  have t1 : HasResidue (slash ((d : ℤ) / 2) (c 1 • R_T) (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phiMinus (c 1 • R_T)) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiMinus_R_T, smul_eq_mul, mul_one]
    have h := (hasResidue_slash_KMinus_T ℓ d hd z hne).const_mul (c 1)
    convert h using 1
    all_goals first | (ext τ; rw [Pi.smul_apply, smul_eq_mul]) | ring
  have t2 : HasResidue (slash ((d : ℤ) / 2) (c 2 • (R_T * R_S)) (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phiMinus (c 2 • (R_T * R_S))) := by
    rw [AlgebraFacts.slash_smul, map_smul, phiMinus_TS, smul_zero, mul_zero]
    have h := (hasResidue_slash_KMinus_TS ℓ d hd z hne).const_mul (c 2)
    rw [mul_zero] at h
    convert h using 1
    all_goals (ext τ; rw [Pi.smul_apply, smul_eq_mul])
  have hthree : HasResidue (slash ((d : ℤ) / 2)
      (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S)) (fun σ : ℍ => KMinus ℓ d σ z)) z
      (-(1 / (2 * Real.pi)) * phiMinus (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S))) := by
    rw [slash_add, slash_add, map_add, map_add]
    convert (t0.add t1).add t2 using 1
    ring
  have hfun : slash ((d : ℤ) / 2) r (fun σ : ℍ => KMinus ℓ d σ z)
      = slash ((d : ℤ) / 2) (r - ∑ i : Fin 3, c i • M3 i) (fun σ : ℍ => KMinus ℓ d σ z)
        + slash ((d : ℤ) / 2) (c 0 • (1 : R) + c 1 • R_T + c 2 • (R_T * R_S))
            (fun σ : ℍ => KMinus ℓ d σ z) := by
    rw [← slash_add, ← hexp]
    congr 1
    abel
  rw [hfun, hφ]
  convert h0.add hthree using 1
  ring

end Work.Residues
