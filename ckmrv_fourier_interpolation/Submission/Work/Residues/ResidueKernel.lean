/-
# The residue theorem of CKMRV Theorem 4.9(3): the analytic input

This file assembles the residues of the kernel `K_+` at the poles `z`, `Tz = z+1` and
`TS·z = (z-1)/z` of the `SL(2,ℤ)`-orbit of `z`, from the explicit computations with the
*cleared* kernels (`Work.Residues.KPlusClear_diag`, `Work.Residues.KPlusClear_T`,
`Work.Residues.KPlusClear_TS`) and the general limit lemma
`Work.Residues.hasResidue_of_cleared`.

## Main results

* `Work.Residues.jprime` : the paper's `j' = -2πiE₄²E₆/Δ`.
* `Work.Residues.AfunPlus` : the cleared kernel divided by `Δ(τ)Δ(z)^e`; its value at a
  pole `τ = γz` is `j'(γz)` times the residue of `K_+` there.
* `Work.Residues.hasResidue_KPlus_self`, `hasResidue_KPlus_T`, `hasResidue_KPlus_TS` : the
  residues of `K_+^{(d)}(·,z)` at the three points of the orbit that occur, with values
  `-(1/2π)φ_+(1)`, `-(1/2π)φ_+(T)` and `-(1/2π)φ_+(TS)`.
-/
import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.Poles
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.hasResidue_smul_SL
import Submission.Work.Residues.tendsto_slope_jInvariantFun
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KPlusClear_T

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## The derivative `j' = -2πiE₄²E₆/Δ` -/

/-- The paper's value of `j' = -2πiE₄²E₆/Δ` (equation (2.7)). -/
def jprime (z : ℍ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I) * E4Fun z ^ 2 * E6Fun z / DeltaFun z

theorem jprime_ne_zero_iff (z : ℍ) : jprime z ≠ 0 ↔ E4Fun z * E6Fun z ≠ 0 := by
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hA : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    rw [neg_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff]
    exact ⟨⟨by norm_num, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  have hnum : -(2 * (Real.pi : ℂ) * Complex.I) * E4Fun z ^ 2 * E6Fun z = 0
      ↔ E4Fun z * E6Fun z = 0 := by
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hA
        · rw [pow_two, mul_self_eq_zero] at h
          rw [h, zero_mul]
      · rw [h, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rw [h]; ring
      · rw [h]; ring
  have hgoal : jprime z = 0 ↔ E4Fun z * E6Fun z = 0 := by
    rw [jprime, div_eq_zero_iff, hnum]
    exact or_iff_left hD
  exact not_congr hgoal

lemma tendsto_slope_jprime (z : ℍ) :
    Tendsto (fun τ : ℍ => (jInvariantFun τ - jInvariantFun z) / ((τ : ℂ) - (z : ℂ)))
      (𝓝[≠] z) (𝓝 (jprime z)) :=
  tendsto_slope_jInvariantFun z

/-! ## The cleared kernel over `Δ(τ)Δ(z)^e` -/

/-- The exponent `e = 1` for `d = 8` and `e = 2` for `d = 24` of Theorem 4.9(4). -/
def dpow (d : ℕ) : ℕ := if d = 8 then 1 else 2

/-- The cleared kernel divided by its `τ`-dependent denominator; its value at a pole
`τ = γz` is `j'(γz)` times the residue of `K_+` there. -/
def AfunPlus (d : ℕ) (z : ℍ) (τ : ℍ) : ℂ :=
  KPlusClear d τ z / (DeltaFun τ * DeltaFun z ^ dpow d)

lemma mdifferentiableAt_AfunPlus (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (τ₀ : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (AfunPlus d z) τ₀ := by
  have h1 : MDiff (fun τ : ℍ => KPlusClear d τ z) :=
    (KernelGrowth.KPlusClear_growth_tau d hd z).1
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => DeltaFun τ * DeltaFun z ^ dpow d) τ₀ :=
    (ClassicalFacts.DeltaFun_mem_InP.1 τ₀).mul mdifferentiableAt_const
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact h1 τ₀
  · exact h2
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ₀)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

/-- The cleared identity: for `τ` with `j τ ≠ j z`, `K_+^{(d)}(τ,z)·(j τ - j z) = AfunPlus d z τ`. -/
lemma mul_slope_eq_AfunPlus (d : ℕ) (hd : d = 8 ∨ d = 24) (z τ : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun z) :
    KPlus d τ z * (jInvariantFun τ - jInvariantFun z) = AfunPlus d z τ := by
  have hlink := ClearLink.KPlusClear_eq_smul d hd τ z h
  rw [AfunPlus, eq_div_iff]
  · rw [hlink]
    simp only [growthPrefactor, dpow]
    ring
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

/-! ## The cleared kernel at `Tz` -/

/-- `AfunPlus d z` at `τ = Tz = z+1` equals `iE₄²E₆/Δ(z)`. -/
lemma AfunPlus_vadd_one (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunPlus d z ((1 : ℝ) +ᵥ z) = Complex.I * E4Fun z ^ 2 * E6Fun z / DeltaFun z := by
  have hD1 : DeltaFun ((1 : ℝ) +ᵥ z) = DeltaFun z := KernelFacts.DeltaFun_vadd_one z
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  rw [AfunPlus, KPlusClear_T d hd z, hD1]
  simp only [dpow]
  rw [mul_div_cancel_right₀ _ (mul_ne_zero hD (pow_ne_zero _ hD))]

/-- `j'(Tz) = j'(z)`. -/
lemma jprime_vadd_one (z : ℍ) : jprime ((1 : ℝ) +ᵥ z) = jprime z := by
  simp only [jprime, KernelFacts.E4Fun_vadd_one, KernelFacts.E6Fun_vadd_one,
    KernelFacts.DeltaFun_vadd_one]

/-- `AfunPlus d z` at `τ = Tz` equals `-(1/2π)·j'(Tz)`. -/
lemma AfunPlus_vadd_one_eq (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunPlus d z ((1 : ℝ) +ᵥ z) = -(1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ z) := by
  rw [AfunPlus_vadd_one d hd z, jprime_vadd_one, jprime]
  have hD : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-! ## The three points of the orbit -/

/-- The residue of `K_+^{(d)}(·,z)` at `τ = z` is `0 = -(1/2π)φ_+(1)`. -/
theorem hasResidue_KPlus_self (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KPlus d τ z) z 0 := by
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KPlus d τ z) (A := AfunPlus d z)
    (z₀ := z) (z := z) (c := jprime z)
    (mdifferentiableAt_AfunPlus d hd z z) rfl (tendsto_slope_jprime z) hne ?_
  · have h : AfunPlus d z z = 0 := by
      simp only [AfunPlus, KPlusClear_diag d hd z, zero_div]
    rw [h, zero_div] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime z).eventually
      (eventually_ne_nhds hne)] with τ hτ hτne
    have hτ' : τ ≠ z := by simpa using hτ
    have hslope : (jInvariantFun τ - jInvariantFun z) / ((τ : ℂ) - (z : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    exact mul_slope_eq_AfunPlus d hd z τ (sub_ne_zero.mp hjnz)

/-- The residue of `K_+^{(d)}(·,z)` at `τ = Tz = z+1` is `-(1/2π)φ_+(T) = -1/(2π)`. -/
theorem hasResidue_KPlus_T (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KPlus d τ z) ((1 : ℝ) +ᵥ z) (-(1 / (2 * Real.pi))) := by
  have hT : jInvariantFun ((1 : ℝ) +ᵥ z) = jInvariantFun z :=
    KernelFacts.jInvariantFun_vadd_one z
  have hneT : jprime ((1 : ℝ) +ᵥ z) ≠ 0 := by
    rw [jprime_ne_zero_iff] at hne ⊢
    rwa [KernelFacts.E4Fun_vadd_one, KernelFacts.E6Fun_vadd_one]
  have hmain := hasResidue_of_cleared (f := fun τ : ℍ => KPlus d τ z) (A := AfunPlus d z)
    (z₀ := (1 : ℝ) +ᵥ z) (z := z) (c := jprime ((1 : ℝ) +ᵥ z))
    (mdifferentiableAt_AfunPlus d hd z _) hT (tendsto_slope_jprime _) hneT ?_
  · have hcancel : -(1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ z) / jprime ((1 : ℝ) +ᵥ z)
        = -(1 / (2 * Real.pi)) := by
      rw [mul_div_assoc, div_self hneT, mul_one]
    rw [AfunPlus_vadd_one_eq d hd z, hcancel] at hmain
    exact hmain
  · filter_upwards [self_mem_nhdsWithin, (tendsto_slope_jprime _).eventually
      (eventually_ne_nhds hneT)] with τ hτ hτne
    have hτ' : τ ≠ (1 : ℝ) +ᵥ z := by simpa using hτ
    have hslope : (jInvariantFun τ - jInvariantFun ((1 : ℝ) +ᵥ z)) /
        ((τ : ℂ) - (((1 : ℝ) +ᵥ z : ℍ) : ℂ)) ≠ 0 := hτne
    have hjnz : jInvariantFun τ - jInvariantFun ((1 : ℝ) +ᵥ z) ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hjnz' : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      have hh := hjnz
      rw [hT] at hh
      exact hh
    exact mul_slope_eq_AfunPlus d hd z τ (sub_ne_zero.mp hjnz')

/-- The residue of `K_+^{(d)}(·,z)` at `τ = Tz` vanishes. -/
theorem hasResidue_KPlus_vadd_one (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) (hne : jprime z ≠ 0) :
    HasResidue (fun τ : ℍ => KPlus d τ z) ((1 : ℝ) +ᵥ z) (-(1 / (2 * Real.pi))) :=
  hasResidue_KPlus_T d hd z hne

end Work.Residues
