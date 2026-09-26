/-
# The residue theorem at every point of the `SL(2,ℤ)`-orbit (CKMRV Theorem 4.9(1)+(3))

Theorem 4.9(3) of CKMRV computes the residue of the slashed kernel at `τ = z`.  Together with
the transformation law of residues under the Möbius action
(`Work.Residues.hasResidue_smul_SL`, the paper's equation (residue1)) this determines the
residue at every point of the `SL(2,ℤ)`-orbit of `z` -- the paper's equation (genpart4) with
`β = 1`, the residue formula used throughout Section 5:

  `Res_{τ = δz}(K_±|^τ_{d/2}(r δ⁻¹)) = -(j(δ,z)^{d/2-2}/2π) φ_±(r)`,

equivalently `Res_{τ = δz}(K_±|^τ_{d/2} r) = -(j(δ,z)^{d/2-2}/2π) φ_±(r δ)`
(`hasResidue_slash_KPlus_orbit'`).

Note the *order* of the group-algebra element: `SlashAction` acts on the function, so by
`Work.Kernels.AlgebraFacts.slash_mul` (`slash k (r*s) F = slash k s (slash k r F)`) the
element is `r * single δ⁻¹`; the residue at `δz` is `j(δ,z)^{k-2}·c₀`, not
`j(δ,z)^{k-2}·φ_±(δ⁻¹ r δ)` (which is what `single δ⁻¹ * r` would give).  Two consistency
checks: `δ = 1` reduces to `Work.Residues.hasResidue_slash_KPlus`, and `δ = T`, `r = R_T`
reduces to `Work.Residues.hasResidue_KPlus_T` (residue `-1/(2π)` at `τ = z + 1`).
-/
import Mathlib
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.hasResidue_smul_SL
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_smul_SL2

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-! ## The transfer step, with the point made explicit

`Work.Residues.hasResidue_smul_SL` is the paper's (residue1).  It is restated here with the
incoming point written as `δ⁻¹ • (δ • z)`, so that the elaborator never has to invert the
action of `SL(2,ℤ)` on `ℍ` (`γ • ?z = z`). -/
lemma hasResidue_transfer_inv (δ : SL(2,ℤ)) (k : ℤ) {f : ℍ → ℂ} {z : ℍ} {c : ℂ}
    (h : HasResidue f z c) :
    HasResidue (fun τ : ℍ => jFun δ⁻¹ (τ : ℂ) ^ (-k) * f (δ⁻¹ • τ)) (δ • z)
      (jFun δ⁻¹ ((δ • z : ℍ) : ℂ) ^ (2 - k) * c) := by
  have h' : HasResidue f (δ⁻¹ • (δ • z)) c := by
    rwa [inv_smul_smul]
  exact hasResidue_smul_SL δ⁻¹ k h'

/-- The factor of automorphy transport: `j(δ⁻¹, δz) = j(δ,z)⁻¹`. -/
lemma jFun_inv_smul_eq_inv (δ : SL(2,ℤ)) (z : ℍ) :
    jFun δ⁻¹ ((δ • z : ℍ) : ℂ) = (jFun δ (z : ℂ))⁻¹ := by
  have h := Work.Kernels.LogLambda.ThetaLower.jFun_mul_cocycle δ⁻¹ δ z
  rw [inv_mul_cancel, Work.Kernels.LogLambda.ThetaLower.jFun_one_apply] at h
  have h2 : jFun δ⁻¹ ((δ • z : ℍ) : ℂ) * jFun δ (z : ℂ) = 1 := h.symm
  calc jFun δ⁻¹ ((δ • z : ℍ) : ℂ)
      = jFun δ⁻¹ ((δ • z : ℍ) : ℂ) * (jFun δ (z : ℂ) * (jFun δ (z : ℂ))⁻¹) := by
        rw [mul_inv_cancel₀ (jFun_ne_zero δ z), mul_one]
    _ = (jFun δ⁻¹ ((δ • z : ℍ) : ℂ) * jFun δ (z : ℂ)) * (jFun δ (z : ℂ))⁻¹ := by ring
    _ = 1 * (jFun δ (z : ℂ))⁻¹ := by rw [h2]
    _ = (jFun δ (z : ℂ))⁻¹ := one_mul _

/-- The automorphy factor of the transported residue: `j(δ⁻¹,δz)^{2-k} = j(δ,z)^{k-2}`. -/
lemma jFun_inv_smul_zpow (δ : SL(2,ℤ)) (z : ℍ) (k : ℤ) :
    jFun δ⁻¹ ((δ • z : ℍ) : ℂ) ^ (2 - k) = jFun δ (z : ℂ) ^ (k - 2) := by
  rw [jFun_inv_smul_eq_inv, _root_.inv_zpow', show -(2 - k) = k - 2 by ring]

/-! ## The orbit residue theorems -/

/-- **Theorem 4.9(1)+(3) at an arbitrary orbit point, for `K_+`.**  For every `δ ∈ SL(2,ℤ)`,
every `r ∈ R` and every `z` with `j'(z) ≠ 0`, the function
`τ ↦ (K_+^{(d)}|^τ_{d/2}(r δ⁻¹))(τ,z)` has residue `-(j(δ,z)^{d/2-2}/2π)φ_+(r)` at `τ = δz`. -/
theorem hasResidue_slash_KPlus_orbit (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (δ : SL(2,ℤ)) (r : R) :
    HasResidue (slash ((d:ℤ)/2) (r * MonoidAlgebra.single δ⁻¹ (1:ℂ))
        (fun σ : ℍ => KPlus d σ z))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2) * (-(1/(2*Real.pi)) * phiPlus r)) := by
  have hbase := hasResidue_slash_KPlus d hd z hne r
  have htr := hasResidue_transfer_inv δ ((d:ℤ)/2) hbase
  have hfun : (fun τ : ℍ => jFun δ⁻¹ (τ : ℂ) ^ (-((d:ℤ)/2)) *
        slash ((d:ℤ)/2) r (fun σ : ℍ => KPlus d σ z) (δ⁻¹ • τ))
      = slash ((d:ℤ)/2) (r * MonoidAlgebra.single δ⁻¹ (1:ℂ))
          (fun σ : ℍ => KPlus d σ z) := by
    rw [Work.Kernels.AlgebraFacts.slash_mul, slash_single, one_smul]
    ext τ
    rw [slash_apply', mul_comm]
  have htr' : HasResidue (fun τ : ℍ => jFun δ⁻¹ (τ : ℂ) ^ (-((d:ℤ)/2)) *
        slash ((d:ℤ)/2) r (fun σ : ℍ => KPlus d σ z) (δ⁻¹ • τ))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2) * (-(1/(2*Real.pi)) * phiPlus r)) := by
    rw [← jFun_inv_smul_zpow δ z ((d:ℤ)/2)]
    exact htr
  rw [hfun] at htr'
  exact htr'

/-- **Theorem 4.9(1)+(3) at an arbitrary orbit point, for `K_-`.** -/
theorem hasResidue_slash_KMinus_orbit (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) (δ : SL(2,ℤ)) (r : R) :
    HasResidue (slash ((d:ℤ)/2) (r * MonoidAlgebra.single δ⁻¹ (1:ℂ))
        (fun σ : ℍ => KMinus ℓ d σ z))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2) * (-(1/(2*Real.pi)) * phiMinus r)) := by
  have hbase := hasResidue_slash_KMinus ℓ d hd z hne r
  have htr := hasResidue_transfer_inv δ ((d:ℤ)/2) hbase
  have hfun : (fun τ : ℍ => jFun δ⁻¹ (τ : ℂ) ^ (-((d:ℤ)/2)) *
        slash ((d:ℤ)/2) r (fun σ : ℍ => KMinus ℓ d σ z) (δ⁻¹ • τ))
      = slash ((d:ℤ)/2) (r * MonoidAlgebra.single δ⁻¹ (1:ℂ))
          (fun σ : ℍ => KMinus ℓ d σ z) := by
    rw [Work.Kernels.AlgebraFacts.slash_mul, slash_single, one_smul]
    ext τ
    rw [slash_apply', mul_comm]
  have htr' : HasResidue (fun τ : ℍ => jFun δ⁻¹ (τ : ℂ) ^ (-((d:ℤ)/2)) *
        slash ((d:ℤ)/2) r (fun σ : ℍ => KMinus ℓ d σ z) (δ⁻¹ • τ))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2) * (-(1/(2*Real.pi)) * phiMinus r)) := by
    rw [← jFun_inv_smul_zpow δ z ((d:ℤ)/2)]
    exact htr
  rw [hfun] at htr'
  exact htr'

/-- The orbit residue in the form obtained by multiplying the group-algebra element by `δ` on
the right: `Res_{τ=δz}(K_±|^τ_{d/2}r) = -(j(δ,z)^{d/2-2}/2π)φ_±(rδ)` (the paper's (genpart4)
with `α = rδ`, `β = 1`). -/
theorem hasResidue_slash_KPlus_orbit' (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (δ : SL(2,ℤ)) (r : R) :
    HasResidue (slash ((d:ℤ)/2) r (fun σ : ℍ => KPlus d σ z))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2)
        * (-(1/(2*Real.pi)) * phiPlus (r * MonoidAlgebra.single δ (1:ℂ)))) := by
  have h := hasResidue_slash_KPlus_orbit d hd z hne δ (r * MonoidAlgebra.single δ (1:ℂ))
  have helem : (r * MonoidAlgebra.single δ (1:ℂ)) * MonoidAlgebra.single δ⁻¹ (1:ℂ) = r := by
    rw [mul_assoc, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
      ← MonoidAlgebra.one_def, mul_one]
  rw [helem] at h
  exact h

/-- The `K_-` analogue of `hasResidue_slash_KPlus_orbit'`. -/
theorem hasResidue_slash_KMinus_orbit' (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) (δ : SL(2,ℤ)) (r : R) :
    HasResidue (slash ((d:ℤ)/2) r (fun σ : ℍ => KMinus ℓ d σ z))
      (δ • z) ((jFun δ (z:ℂ)) ^ ((d:ℤ)/2 - 2)
        * (-(1/(2*Real.pi)) * phiMinus (r * MonoidAlgebra.single δ (1:ℂ)))) := by
  have h := hasResidue_slash_KMinus_orbit ℓ d hd z hne δ (r * MonoidAlgebra.single δ (1:ℂ))
  have helem : (r * MonoidAlgebra.single δ (1:ℂ)) * MonoidAlgebra.single δ⁻¹ (1:ℂ) = r := by
    rw [mul_assoc, MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul,
      ← MonoidAlgebra.one_def, mul_one]
  rw [helem] at h
  exact h

end Work.Residues
