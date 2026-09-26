/-
# The *removable coincidence* in the second variable

CKMRV §5.3 (the paragraph before Figure 9) computes the residue of the integrand
`z ↦ K(τ,z)` at the coincidence point `z = ST^{-1}τ = -1/(τ-1)`: for `α ∈ PSL₂(ℤ)` there is a
pole at `z = α τ` iff `φ(α^{-1}) ≠ 0`, and

  `Res_{z = α τ} K(τ,z) = φ(α^{-1}) / (2π j(α,τ)^{d/2})`.

For `α = ST^{-1}` the group element is `(ST^{-1})^{-1} = TS` and `φ(TS) = 0`, so **there is no
pole at the coincidence `ST^{-1}τ`**.  This is what allows the contour of the layer
continuation to be swept across the line `Re τ = 1` and across the bottom semicircles without
paying a correction term.

The vanishing of the cleared kernel at the coincidence pair `(τ, ST^{-1}τ)` is *not* a new
computation: the coincidence `z₀ = ST^{-1} τ` satisfies `(T S) • z₀ = τ` (the two parabolic
elements `ST^{-1}` and `(TS)^{-1}` agree on `ℍ` because they differ by the central element
`-I`), so

  `K_±^{clear}(τ, z₀) = K_±^{clear}((TS)•z₀, z₀) = 0`

by `Work.Residues.KPlusClear_TS` / `KMinusClear_TS` (CKMRV's `φ_±(TS) = 0`).

## Main results

* `Work.LayerCont.KfunClear_coinc_zero` : `K^{clear}(τ, ST^{-1}τ) = 0`;
* `Work.LayerCont.hasResidue_Kfun_coinc` : `Res_{z = ST^{-1}τ} K(τ,z) = 0`.
-/
import Mathlib
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Kernels.KernelGrowth

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.LayerCont

open Work.Kernels

/-! ## The coincidence as an `SL(2,ℤ)`-translate -/

/-- The coincidence `ST^{-1} τ = -1/(τ-1)` written as the `S`-translate of `T^{-1} τ`. -/
lemma coinc_eq (τ : ℍ) :
    ModularGroup.S • ((-1 : ℝ) +ᵥ τ)
      = (ModularGroup.S * ModularGroup.T⁻¹) • τ := by
  rw [mul_smul, Work.Residues.T_inv_smul_eq]

/-- `S • (S • τ) = τ`, in the `SL(2,ℤ)`-action on `ℍ`. -/
lemma S_smul_S_smul' (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  simp only [UpperHalfPlane.modular_S_smul]
  rw [UpperHalfPlane.ext_iff]
  simp

/-- **`(T S)` undoes the coincidence**: `(T S) • (ST^{-1} • τ) = τ`, because
`(T S)(S T^{-1}) = T (S S) T^{-1} = -I`. -/
lemma TS_smul_coinc (τ : ℍ) :
    (ModularGroup.T * ModularGroup.S) • ((ModularGroup.S * ModularGroup.T⁻¹) • τ) = τ := by
  calc (ModularGroup.T * ModularGroup.S) • ((ModularGroup.S * ModularGroup.T⁻¹) • τ)
      = ModularGroup.T • (ModularGroup.S • (ModularGroup.S • (ModularGroup.T⁻¹ • τ))) := by
        rw [mul_smul, mul_smul]
    _ = ModularGroup.T • (ModularGroup.T⁻¹ • τ) := by rw [S_smul_S_smul']
    _ = τ := by rw [← mul_smul, mul_inv_cancel, one_smul]

/-! ## The cleared kernel vanishes at the coincidence -/

/-- **The cleared kernel `K^{(d)}` vanishes at the coincidence pair `(τ, ST^{-1}τ)`.**

This is CKMRV's statement that the residue at `z = ST^{-1}τ` is proportional to `φ(TS) = 0`:
the pair `(τ, ST^{-1}τ)` is, in the first variable, the pair `(T S • z₀, z₀)` for
`z₀ = ST^{-1} τ`. -/
theorem KfunClear_coinc_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    KfunClear ℓ d τ (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) = 0 := by
  set z₀ : ℍ := (ModularGroup.S * ModularGroup.T⁻¹) • τ with hz₀
  have h1 : ModularGroup.S • ((-1 : ℝ) +ᵥ τ) = z₀ := coinc_eq τ
  rw [h1]
  have h2 : (ModularGroup.T * ModularGroup.S) • z₀ = τ := TS_smul_coinc τ
  rw [← h2]
  have h3 : (ModularGroup.T * ModularGroup.S) • z₀
      = (1 : ℝ) +ᵥ (ModularGroup.S • z₀) := Work.Residues.T_mul_S_smul z₀
  rw [h3, KfunClear, Work.Residues.KPlusClear_TS d hd z₀,
    Work.Residues.KMinusClear_TS ℓ d hd z₀]
  ring

/-! ## The residue at the coincidence vanishes -/

/-- `j'(ST^{-1} τ) ≠ 0` whenever `j'(τ) ≠ 0` (the two differ by the non-zero factor `(τ-1)²`). -/
lemma jprime_coinc_ne_zero (τ : ℍ) (hne : Work.Residues.jprime τ ≠ 0) :
    Work.Residues.jprime (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) ≠ 0 := by
  have hu : (((-1 : ℝ) +ᵥ τ : ℍ) : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero _
  have h4 : E4Fun (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) =
      (((-1 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ 4 * E4Fun τ := by
    rw [Work.Residues.E4Fun_S_smul, Work.Residues.E4Fun_vadd_neg_one]
  have h6 : E6Fun (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) =
      (((-1 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ 6 * E6Fun τ := by
    rw [Work.Residues.E6Fun_S_smul, Work.Residues.E6Fun_vadd_neg_one]
  rw [Work.Residues.jprime_ne_zero_iff] at hne ⊢
  rw [h4, h6]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hu) (mul_ne_zero_iff.mp hne).1)
    (mul_ne_zero (pow_ne_zero 6 hu) (mul_ne_zero_iff.mp hne).2)

/-- **The residue of `ζ ↦ K^{(d)}(τ,ζ)` at the removable coincidence `ζ = ST^{-1}τ` is `0`.**

This is the exact analytic input for the residue-free contour shift of CKMRV §5.3: the pole
rectangle of the layer continuation at the coincidence height gets no contribution. -/
theorem hasResidue_Kfun_coinc (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (hne : Work.Residues.jprime τ ≠ 0) :
    Work.Residues.HasResidue (fun ζ : ℍ => Kfun ℓ d τ ζ)
      (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) 0 := by
  set ζ₀ : ℍ := ModularGroup.S • ((-1 : ℝ) +ᵥ τ) with hζ₀
  have hj : jInvariantFun ζ₀ = jInvariantFun τ := by
    rw [hζ₀, KernelFacts.jInvariantFun_S_smul, Work.Residues.jInvariantFun_vadd_neg_one]
  have hne' : Work.Residues.jprime ζ₀ ≠ 0 := jprime_coinc_ne_zero τ hne
  have hA : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => -(Work.Residues.AfunPlus d ζ τ + Work.Residues.AfunMinus ℓ d ζ τ)) ζ₀ :=
    ((Work.Residues.mdifferentiableAt_AfunPlus_snd d hd τ ζ₀).add
      (Work.Residues.mdifferentiableAt_AfunMinus_snd ℓ d hd τ ζ₀)).neg
  have hmain := Work.Residues.hasResidue_of_cleared
    (f := fun ζ : ℍ => (2 : ℂ) * Kfun ℓ d τ ζ)
    (A := fun ζ : ℍ => -(Work.Residues.AfunPlus d ζ τ + Work.Residues.AfunMinus ℓ d ζ τ))
    (z := τ) (z₀ := ζ₀) (c := Work.Residues.jprime ζ₀) hA hj
    (Work.Residues.tendsto_slope_jprime ζ₀) hne' ?_
  · -- the residue value `A ζ₀ / j' ζ₀` vanishes because the cleared kernel does
    have hzero : Work.Residues.AfunPlus d ζ₀ τ + Work.Residues.AfunMinus ℓ d ζ₀ τ = 0 := by
      have hc : KPlusClear d τ ζ₀ + KMinusClear ℓ d τ ζ₀ = 0 := by
        have h := KfunClear_coinc_zero ℓ d hd τ
        rw [← hζ₀, KfunClear] at h
        have h2 := congrArg (fun x : ℂ => 2 * x) h
        simpa using h2
      rw [Work.Residues.AfunPlus, Work.Residues.AfunMinus, ← add_div, hc, zero_div]
    have hval : -(Work.Residues.AfunPlus d ζ₀ τ + Work.Residues.AfunMinus ℓ d ζ₀ τ)
        / Work.Residues.jprime ζ₀ = 0 := by rw [hzero]; simp
    rw [hval] at hmain
    -- `2 * K = K` up to the harmless factor `2`
    have hfin : (fun ζ : ℍ => Kfun ℓ d τ ζ)
        = fun ζ : ℍ => (2 : ℂ)⁻¹ * ((2 : ℂ) * Kfun ℓ d τ ζ) := by
      funext ζ; ring
    rw [hfin]
    simpa only [mul_zero] using hmain.const_mul ((2 : ℂ)⁻¹)
  · filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime ζ₀).eventually (eventually_ne_nhds hne')]
      with ζ hζ hζne
    have hslope : (jInvariantFun ζ - jInvariantFun ζ₀) / ((ζ : ℂ) - (ζ₀ : ℂ)) ≠ 0 := hζne
    have hjnz : jInvariantFun ζ - jInvariantFun τ ≠ 0 := by
      intro h0; exact hslope (by rw [hj, h0, zero_div])
    have hp := Work.Residues.mul_slope_eq_AfunPlus_snd d hd τ ζ (sub_ne_zero.mp hjnz)
    have hm := Work.Residues.mul_slope_eq_AfunMinus_snd ℓ d hd τ ζ (sub_ne_zero.mp hjnz)
    show (2 : ℂ) * Kfun ℓ d τ ζ * (jInvariantFun ζ - jInvariantFun τ)
      = -(Work.Residues.AfunPlus d ζ τ + Work.Residues.AfunMinus ℓ d ζ τ)
    rw [Work.Kernels.Kfun_eq]
    have hA' : -(KPlus d τ ζ * (jInvariantFun ζ - jInvariantFun τ))
        = Work.Residues.AfunPlus d ζ τ := by rw [hp]; ring
    have hB' : -(KMinus ℓ d τ ζ * (jInvariantFun ζ - jInvariantFun τ))
        = Work.Residues.AfunMinus ℓ d ζ τ := by rw [hm]; ring
    rw [← hA', ← hB']; ring

end Work.LayerCont
