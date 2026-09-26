/-
# Vanishing of the cleared kernel at orbit points annihilated by `φ = (φ₊ + φ₋)/2`

For `δ ∈ SL(2,ℤ)` whose image in the group algebra satisfies
`φ₊(δ) + φ₋(δ) = 0` (equivalently `φ(δ) = 0`, CKMRV (3.12)), the cleared kernel of
CKMRV Theorem 4.9 vanishes at the corresponding orbit point:

  `KfunClear ℓ d (δ • z) z = 0`   whenever `j'(z) ≠ 0`.

The mechanism is the residue theorem of CKMRV Theorem 4.9(3) in its orbit form: for `r = 1`
the function `σ ↦ K^{(d)}(σ,z)` has residue
`j(δ,z)^{d/2-2} · (-(1/2π)) · (φ₊(δ) + φ₋(δ))/2` at `σ = δz`, which vanishes by hypothesis.
On the other hand `hasResidue_of_cleared` identifies this residue with
`AfunFun ℓ d (δz) z / j'(δz)`, where `AfunFun` is the cleared kernel divided by
`Δ(σ)Δ(z)^e`; uniqueness of residues gives `AfunFun ℓ d (δz) z = 0`, whence the claim since
`KfunClear ℓ d τ z = Δ(τ)Δ(z)^e · AfunFun ℓ d τ z`.

## Main results

* `Work.Asymptotics.KfunClear_vanish_of_phiPair` : the statement.
* `Work.Asymptotics.jInvariantFun_smul_of_slash`, `jprime_smul_of_slash`,
  `jprime_smul_ne_zero_of_slash` : the modular transformation of `j` and `j'`.
* `Work.Asymptotics.KfunClear_eq_mul_AfunFun` : `KfunClear = Δ(τ)Δ(z)^e · AfunFun`.
-/
import Mathlib
import Submission.Work.Residues.ResidueOrbit
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.differentiableOn_AfunFun_fst
import Submission.Work.Kernels.KernelFacts.fk_slash

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

open Work.Kernels Work.Residues

/-- `E₄` under the modular action: `E₄(γ•z) = E₄(z)·j(γ,z)⁴`. -/
lemma E4Fun_smul_of_slash (γ : SL(2,ℤ)) (z : ℍ) :
    E4Fun (γ • z) = E4Fun z * (jFun γ (z : ℂ)) ^ (4 : ℤ) := by
  have h := congr_fun (Work.Kernels.KernelFacts.E4Fun_slash γ) z
  rw [Kernels.slash_apply'] at h
  have h4 : (jFun γ (z : ℂ)) ^ (4 : ℤ) ≠ 0 := zpow_ne_zero 4 (jFun_ne_zero γ z)
  have h' : E4Fun (γ • z) / (jFun γ (z : ℂ)) ^ (4 : ℤ) = E4Fun z := by
    simpa [div_eq_mul_inv, _root_.zpow_neg] using h
  rw [div_eq_iff h4] at h'
  exact h'

/-- `E₆` under the modular action: `E₆(γ•z) = E₆(z)·j(γ,z)⁶`. -/
lemma E6Fun_smul_of_slash (γ : SL(2,ℤ)) (z : ℍ) :
    E6Fun (γ • z) = E6Fun z * (jFun γ (z : ℂ)) ^ (6 : ℤ) := by
  have h := congr_fun (Work.Kernels.KernelFacts.E6Fun_slash γ) z
  rw [Kernels.slash_apply'] at h
  have h6 : (jFun γ (z : ℂ)) ^ (6 : ℤ) ≠ 0 := zpow_ne_zero 6 (jFun_ne_zero γ z)
  have h' : E6Fun (γ • z) / (jFun γ (z : ℂ)) ^ (6 : ℤ) = E6Fun z := by
    simpa [div_eq_mul_inv, _root_.zpow_neg] using h
  rw [div_eq_iff h6] at h'
  exact h'

/-- `Δ` under the modular action: `Δ(γ•z) = Δ(z)·j(γ,z)¹²`. -/
lemma DeltaFun_smul_of_slash (γ : SL(2,ℤ)) (z : ℍ) :
    DeltaFun (γ • z) = DeltaFun z * (jFun γ (z : ℂ)) ^ (12 : ℤ) := by
  have h := congr_fun (Work.Kernels.KernelFacts.DeltaFun_slash γ) z
  rw [Kernels.slash_apply'] at h
  have h12 : (jFun γ (z : ℂ)) ^ (12 : ℤ) ≠ 0 := zpow_ne_zero 12 (jFun_ne_zero γ z)
  have h' : DeltaFun (γ • z) / (jFun γ (z : ℂ)) ^ (12 : ℤ) = DeltaFun z := by
    simpa [div_eq_mul_inv, _root_.zpow_neg] using h
  rw [div_eq_iff h12] at h'
  exact h'

/-- The `j`-invariant is invariant under the full modular group. -/
lemma jInvariantFun_smul_of_slash (γ : SL(2,ℤ)) (z : ℍ) :
    jInvariantFun (γ • z) = jInvariantFun z := by
  have h4 := E4Fun_smul_of_slash γ z
  have h12 := DeltaFun_smul_of_slash γ z
  have hj : jFun γ (z : ℂ) ≠ 0 := jFun_ne_zero γ z
  simp only [jInvariantFun, h4, h12]
  field_simp

/-- The derivative of `j` transforms as `j'(γ•z) = j'(z)·j(γ,z)²`. -/
lemma jprime_smul_of_slash (γ : SL(2,ℤ)) (z : ℍ) :
    jprime (γ • z) = jprime z * (jFun γ (z : ℂ)) ^ (2 : ℤ) := by
  have h4 := E4Fun_smul_of_slash γ z
  have h6 := E6Fun_smul_of_slash γ z
  have h12 := DeltaFun_smul_of_slash γ z
  have hΔ : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hj : jFun γ (z : ℂ) ≠ 0 := jFun_ne_zero γ z
  simp only [jprime, h4, h6, h12]
  rw [zpow_two]
  field_simp

/-- `j'` does not vanish on the modular orbit of a point where it does not vanish. -/
lemma jprime_smul_ne_zero_of_slash (γ : SL(2,ℤ)) (z : ℍ) (h : jprime z ≠ 0) :
    jprime (γ • z) ≠ 0 := by
  rw [jprime_smul_of_slash]
  exact mul_ne_zero h (zpow_ne_zero 2 (jFun_ne_zero γ z))

/-- `KfunClear` is `Δ(τ)Δ(z)^e` times `AfunFun`. -/
lemma KfunClear_eq_mul_AfunFun (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    KfunClear ℓ d τ z = DeltaFun τ * DeltaFun z ^ dpow d * AfunFun ℓ d τ z := by
  have hτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hD : DeltaFun τ * DeltaFun z ^ dpow d ≠ 0 := mul_ne_zero hτ (pow_ne_zero _ hz)
  simp only [KfunClear, AfunFun, AfunPlus, AfunMinus]
  field_simp

theorem KfunClear_vanish_of_phiPair (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hδ : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
        + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0) :
    ∀ z : UpperHalfPlane, Work.Residues.jprime z ≠ 0 →
      Work.Kernels.KfunClear ℓ d (δ • z) z = 0 := by
  intro z hz
  -- The residue of `σ ↦ K(σ,z)` at `δ•z` is a multiple of `φ₊(δ) + φ₋(δ) = 0`.
  have hres : Work.Residues.HasResidue (fun σ : ℍ => Work.Kernels.Kfun ℓ d σ z) (δ • z) 0 := by
    have hp := Work.Residues.hasResidue_slash_KPlus_orbit' d hd z hz δ (1 : Work.Kernels.R)
    have hm := Work.Residues.hasResidue_slash_KMinus_orbit' ℓ d hd z hz δ (1 : Work.Kernels.R)
    simp only [Work.Kernels.slash_one, one_mul] at hp hm
    have hsum := (hp.const_mul (1 / 2 : ℂ)).add (hm.const_mul (1 / 2 : ℂ))
    have hfun : ((fun τ : ℍ => (1 / 2 : ℂ) * Work.Kernels.KPlus d τ z)
        + fun τ : ℍ => (1 / 2 : ℂ) * Work.Kernels.KMinus ℓ d τ z)
        = fun σ : ℍ => Work.Kernels.Kfun ℓ d σ z := by
      funext σ; simp only [Pi.add_apply, Work.Kernels.Kfun]; ring
    rw [hfun] at hsum
    convert hsum using 1
    have hkey : (1 / 2 : ℂ)
          * ((jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2)
              * (-(1 / (2 * Real.pi)) * Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))))
        + (1 / 2 : ℂ)
          * ((jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2)
              * (-(1 / (2 * Real.pi)) * Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ))))
        = (1 / 2 : ℂ) * (jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2) * (-(1 / (2 * Real.pi)))
          * (Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
              + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ))) := by ring
    rw [hkey, hδ, mul_zero]
  -- `j` and `j'` at the orbit point `δ•z`.
  have hjinv : jInvariantFun (δ • z) = jInvariantFun z := jInvariantFun_smul_of_slash δ z
  have hjp : jprime (δ • z) ≠ 0 := jprime_smul_ne_zero_of_slash δ z hz
  -- The residue is also `AfunFun (δz) z / j'(δz)`.
  have hclear : Work.Residues.HasResidue (fun σ : ℍ => Work.Kernels.Kfun ℓ d σ z) (δ • z)
      (AfunFun ℓ d (δ • z) z / jprime (δ • z)) := by
    refine Work.Residues.hasResidue_of_cleared
      (f := fun σ : ℍ => Work.Kernels.Kfun ℓ d σ z)
      (A := fun σ : ℍ => AfunFun ℓ d σ z) (z := z) (z₀ := δ • z) (c := jprime (δ • z))
      (mdifferentiable_AfunFun_fst ℓ d hd z (δ • z)) hjinv
      (Work.Residues.tendsto_slope_jprime (δ • z)) hjp ?_
    filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime (δ • z)).eventually
        (eventually_ne_nhds hjp)] with σ hσ hσne
    have hslope : (jInvariantFun σ - jInvariantFun (δ • z)) /
        ((σ : ℂ) - ((δ • z : ℍ) : ℂ)) ≠ 0 := hσne
    have hne : jInvariantFun σ - jInvariantFun (δ • z) ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hne' : jInvariantFun σ - jInvariantFun z ≠ 0 := by
      rw [← hjinv]; exact hne
    exact Kfun_mul_slope_eq_AfunFun ℓ d hd σ z (sub_ne_zero.mp hne')
  -- Uniqueness of the residue: `AfunFun (δz) z = 0`.
  have hAf : AfunFun ℓ d (δ • z) z = 0 := by
    have huniq := hclear.unique hres
    rcases div_eq_zero_iff.mp huniq with h | h
    · exact h
    · exact absurd h hjp
  rw [KfunClear_eq_mul_AfunFun ℓ d (δ • z) z, hAf, mul_zero]

end Work.Asymptotics
