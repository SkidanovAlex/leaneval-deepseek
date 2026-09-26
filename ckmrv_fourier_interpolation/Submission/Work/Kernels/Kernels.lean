/-
# The integral kernels `K`, `K_±` of CKMRV (Theorem 4.9)

This file gives the *explicit* kernels of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska,
Ann. of Math. 196 (2022)), Theorem 4.9 (labelled `thm: K` in the paper), for `d = 8` and
`d = 24`, following the formulas of Section 4.4.

The construction is

  `K_+^{(d)}(τ,z) = φ⃗(τ)ᵗ · Υ_+^{(d)}(τ,z) · φ̃⃗(z)`,
  `K_-^{(d)}(τ,z) = ψ⃗(τ)ᵗ · Υ_-^{(d)}(τ,z) · ψ̃⃗(z)`,
  `K^{(d)} = (K_+^{(d)} + K_-^{(d)})/2`,  `K̂^{(d)} = (K_+^{(d)} - K_-^{(d)})/2`,

where

* `φ_{-2}(τ) = τ`, `φ_0(τ) = τE₂(τ) - 3i/π`, `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)`
  (`Work.Kernels.phiNeg2`, `phi0`, `phi2`), the basis of `Ann_{d/2}(𝓘₊, 𝒫)` predicted by
  Proposition 4.2;
* `φ̃_{-2}(z) = z²`, `φ̃_0(z) = z²(E₂|₂S)(z)`, `φ̃_2(z) = z²((E₂|₂S)(z))²`
  (`Work.Kernels.phitVec`), the basis of `Ann_{2-d/2}(𝓘̃₊, 𝒫)` of Proposition 4.4;
* `ψ_0 = 1`, `ψ_2 = ξ₂𝓛 + (ξ₂|₂S)𝓛_S`, `ψ_4 = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` and
  `ψ̃_0 = 𝓛`, `ψ̃_2 = W`, `ψ̃_4 = U² - V²` (`Work.Kernels.psiVec`, `psitVec`),
  the bases of Proposition 4.3 and 4.5;
* the matrices `Υ_±^{(d)}` are given by the explicit formulas of Section 4.4, with
  `(f_{-2}, f_0, f_2, …, f_14) = (E₁₀/Δ, 1, E₁₄/Δ, E₄, E₆, E₈, E₁₀, Δ, E₁₄)`
  (`Work.Kernels.fk`) and `Π_{k₁,k₂,k₃} = diag(f_{k₁},f_{k₂},f_{k₃})`
  (`Work.Kernels.PiMat`).

The two logarithm functions `𝓛`, `𝓛_S` of the paper are *not* constructed here; they are
introduced as the data of `Work.Kernels.LogLambdaData`, whose fields are the transformation
laws (2.9) of the paper, so that `K_-` is defined relative to such data.

## Main definitions

* `Work.Kernels.LogLambdaData` : `𝓛` and `𝓛_S`.
* `Work.Kernels.phiVec`, `phitVec`, `psiVec`, `psitVec` : the four basis vectors.
* `Work.Kernels.fk`, `PiMat` : the `f_k` and the diagonal matrices `Π`.
* `Work.Kernels.UpsilonPlus`, `UpsilonMinus` : the coefficient matrices.
* `Work.Kernels.KPlus`, `KMinus`, `Kfun`, `Khat` : the kernels.
* `Work.Kernels.HasSimplePoleWithResidue` : a precise meaning for "simple pole at `z` with
  residue `c`".
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.GroupAlgebra

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-! ## The logarithm functions `𝓛`, `𝓛_S` of the paper -/

/-- The data `(𝓛, 𝓛_S)` of CKMRV Section 2.1.5: the normalised logarithms of `λ` and `λ_S`,
satisfying `e^𝓛 = λ`, `e^{𝓛_S} = λ_S` and the transformation laws (2.9) of the paper. -/
structure LogLambdaData where
  /-- `𝓛`, the normalised logarithm of `λ`. -/
  L : ℍ → ℂ
  /-- `𝓛_S`, the normalised logarithm of `λ_S = 1 - λ`. -/
  L_S : ℍ → ℂ
  holo : MDiff L
  holo_S : MDiff L_S
  memP : ModerateGrowthOn Set.univ L
  memP_S : ModerateGrowthOn Set.univ L_S
  exp_L : ∀ τ, Complex.exp (L τ) = lambdaFun τ
  exp_L_S : ∀ τ, Complex.exp (L_S τ) = lambdaSFun τ
  slash_T : ∀ τ, (L ∣[(0 : ℤ)] ModularGroup.T) τ = L τ - L_S τ + (Real.pi : ℂ) * Complex.I
  slash_T_S : ∀ τ, (L_S ∣[(0 : ℤ)] ModularGroup.T) τ = - L_S τ
  slash_S : L ∣[(0 : ℤ)] ModularGroup.S = L_S
  slash_S_S : L_S ∣[(0 : ℤ)] ModularGroup.S = L

/-! ## The basis functions `φ`, `φ̃`, `ψ`, `ψ̃` -/

/-- `φ_{-2}(τ) = τ`. -/
def phiNeg2 : ℍ → ℂ := fun τ => (τ : ℂ)

/-- `φ_0(τ) = τE₂(τ) - 3i/π`. -/
def phi0 : ℍ → ℂ := fun τ => (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)

/-- `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)`. -/
def phi2 : ℍ → ℂ :=
  fun τ => (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ

/-- The vector `(φ_{-2}, φ_0, φ_2)` of Proposition 4.2. -/
def phiVec : ℍ → Fin 3 → ℂ := fun τ => ![phiNeg2 τ, phi0 τ, phi2 τ]

/-- `(E₂|₂S)(z) = z^{-2}E₂(-1/z)`, the second `τ`-translate of `E₂` appearing in
Proposition 4.4. -/
def E2S : ℍ → ℂ := fun z => (E2Fun ∣[(2 : ℤ)] ModularGroup.S) z

/-- The vector `(φ̃_{-2}, φ̃_0, φ̃_2) = (z², z²(E₂|₂S)(z), z²((E₂|₂S)(z))²)` of
Proposition 4.4. -/
def phitVec : ℍ → Fin 3 → ℂ :=
  fun z => ![(z : ℂ) ^ 2, (z : ℂ) ^ 2 * E2S z, (z : ℂ) ^ 2 * (E2S z) ^ 2]

/-- `ψ_2 = ξ₂𝓛 + (ξ₂|₂S)𝓛_S` of Proposition 4.3. -/
def psi2 (ℓ : LogLambdaData) : ℍ → ℂ :=
  fun τ => xi2Fun τ * ℓ.L τ + (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ

/-- `ψ_4 = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` of Proposition 4.3. -/
def psi4 (ℓ : LogLambdaData) : ℍ → ℂ :=
  fun τ => xi4Fun τ * ℓ.L τ + (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ

/-- The vector `(ψ_0, ψ_2, ψ_4)` of Proposition 4.3. -/
def psiVec (ℓ : LogLambdaData) : ℍ → Fin 3 → ℂ :=
  fun τ => ![1, psi2 ℓ τ, psi4 ℓ τ]

/-- The vector `(ψ̃_0, ψ̃_2, ψ̃_4) = (𝓛, W, U² - V²)` of Proposition 4.5. -/
def psitVec (ℓ : LogLambdaData) : ℍ → Fin 3 → ℂ :=
  fun z => ![ℓ.L z, WFun z, UFun z ^ 2 - VFun z ^ 2]

/-! ## The functions `f_k` and the matrices `Π` -/

/-- The list `(f_{-2}, f_0, f_2, …, f_14) = (E₁₀/Δ, 1, E₁₄/Δ, E₄, E₆, E₈, E₁₀, Δ, E₁₄)`
of CKMRV Section 4.4, extended by `0` off the listed weights. -/
def fk (k : ℤ) (τ : ℍ) : ℂ :=
  if k = -2 then E10Fun τ / DeltaFun τ
  else if k = 0 then 1
  else if k = 2 then E14Fun τ / DeltaFun τ
  else if k = 4 then E4Fun τ
  else if k = 6 then E6Fun τ
  else if k = 8 then E8Fun τ
  else if k = 10 then E10Fun τ
  else if k = 12 then DeltaFun τ
  else if k = 14 then E14Fun τ
  else 0

/-- The diagonal matrix `Π_{k₁,k₂,k₃}(τ) = diag(f_{k₁}(τ), f_{k₂}(τ), f_{k₃}(τ))`. -/
def PiMat (v : Fin 3 → ℤ) (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => fk (v i) τ

/-! ## The coefficient matrices `Υ_±` -/

/-- `1728`. -/
def c1728 : ℂ := 1728

/-- The coefficient matrix `Υ_+^{(d)}` of CKMRV Section 4.4 (vanishing for `d ∉ {8,24}`). -/
def UpsilonPlus (d : ℕ) (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let jτ := jInvariantFun τ
  let jz := jInvariantFun z
  let jτz := jτ - jz
  if d = 8 then
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z * jτz)⁻¹ •
      (PiMat ![6, 4, 2] τ * !![jτz, 0, 1; -2 * jτz, -2, 0; 1, 0, 0] *
        PiMat ![12, 10, 8] z)
  else if d = 24 then
    ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ •
      (PiMat ![14, 12, 10] τ *
        !![6, 0, c1728 * jτz⁻¹ - 6;
           -12 * jτ + 5 * c1728, -2 * c1728 * jτz⁻¹, 12 * jτ - 7 * c1728;
           c1728 * jτz⁻¹ + 6, 0, -6] *
        PiMat ![4, 2, 0] z)
  else 0

/-- The coefficient matrix `Υ_-^{(d)}` of CKMRV Section 4.4 (vanishing for `d ∉ {8,24}`). -/
def UpsilonMinus (d : ℕ) (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let jτ := jInvariantFun τ
  let jz := jInvariantFun z
  let jτz := jτ - jz
  if d = 8 then
    ((2 : ℂ) * c1728 * (Real.pi : ℂ) * DeltaFun z * jτz)⁻¹ •
      (PiMat ![4, 2, 0] τ *
        !![-2 * c1728, 0, 0; 0, 1, -1; 0, c1728 - jτ, jτ] *
        PiMat ![10, 8, 6] z)
  else if d = 24 then
    ((2 : ℂ) * c1728 * (Real.pi : ℂ) * DeltaFun z * jτz)⁻¹ •
      (PiMat ![12, 10, 8] τ *
        !![-2 * c1728, -2 * c1728 * jτz, 0;
           0, jτ + 2 * jτz, -1;
           0, c1728 - 2 * jτz - jτ, 1] *
        PiMat ![2, 0, -2] z)
  else 0

/-! ## The kernels -/

/-- `K_+^{(d)}(τ,z) = φ⃗(τ)ᵗ · Υ_+^{(d)}(τ,z) · φ̃⃗(z)`. -/
def KPlus (d : ℕ) (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, phiVec τ i * UpsilonPlus d τ z i j * phitVec z j

/-- `K_-^{(d)}(τ,z) = ψ⃗(τ)ᵗ · Υ_-^{(d)}(τ,z) · ψ̃⃗(z)`. -/
def KMinus (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, psiVec ℓ τ i * UpsilonMinus d τ z i j * psitVec ℓ z j

/-- `K^{(d)} = (K_+^{(d)} + K_-^{(d)})/2`. -/
def Kfun (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (KPlus d τ z + KMinus ℓ d τ z) / 2

/-- `K̂^{(d)} = (K_+^{(d)} - K_-^{(d)})/2 = -K^{(d)}|^τ_{d/2}S`. -/
def Khat (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (KPlus d τ z - KMinus ℓ d τ z) / 2

/-! ## Growth: the kernels with the poles cleared

Theorem 4.9(4) of the paper says that `Δ(τ)Δ(z)(j(τ)−j(z))K^{(8)}_±(τ,z)` and
`Δ(τ)Δ(z)²(j(τ)−j(z))K^{(24)}_±(τ,z)` lie in `𝒫`.  Since `K_±` has a simple pole precisely
where `j(τ) = j(z)`, the product form `growthPrefactor · K_±` is *not* holomorphic in Lean's
convention `0⁻¹ = 0` (the product takes the value `0` at `j(τ) = j(z)`, while its limit is
generically non-zero).  We therefore define the *cleared* kernels explicitly, with the factor
`(j(τ)−j(z))` multiplied into the numerator and no division by `j(τ)−j(z)` anywhere.
-/

/-- The prefactor `Δ(τ)Δ(z)^{1}(j(τ)−j(z))` (for `d = 8`) resp. `Δ(τ)Δ(z)^{2}(j(τ)−j(z))`
(for `d = 24`) of Theorem 4.9(4).  It equals `Δ(τ)Δ(z)^e(j(τ)−j(z))` and is used only to
state the agreement of the cleared kernels with the kernels off the exceptional set. -/
def growthPrefactor (d : ℕ) (τ z : ℍ) : ℂ :=
  DeltaFun τ * DeltaFun z ^ (if d = 8 then 1 else 2) * (jInvariantFun τ - jInvariantFun z)

/-- `Δ(τ) · Π_{k₁,k₂,k₃}(τ)`: the diagonal matrix whose entries are `Δ(τ)f_{k_i}(τ)`
(holomorphic on `ℍ` because `Δ` is nowhere zero). -/
def PiMatDelta (v : Fin 3 → ℤ) (τ : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => DeltaFun τ * fk (v i) τ

/-- `Δ(τ)Δ(z)^{e}(j(τ)−j(z)) · Υ_+^{(d)}(τ,z)`, written without any division by
`j(τ)−j(z)`. -/
def UpsilonPlusClear (d : ℕ) (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let jτ := jInvariantFun τ
  let jz := jInvariantFun z
  let J := jτ - jz
  if d = 8 then
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
      (PiMatDelta ![6, 4, 2] τ * !![J, 0, 1; -2 * J, -2, 0; 1, 0, 0] *
        PiMat ![12, 10, 8] z)
  else if d = 24 then
    ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ •
      (PiMatDelta ![14, 12, 10] τ *
        !![6 * J, 0, c1728 - 6 * J;
           -12 * jτ * J + 5 * c1728 * J, -2 * c1728, 12 * jτ * J - 7 * c1728 * J;
           c1728 + 6 * J, 0, -6 * J] *
        (DeltaFun z • PiMat ![4, 2, 0] z))
  else 0

/-- `Δ(τ)Δ(z)^{e}(j(τ)−j(z)) · Υ_-^{(d)}(τ,z)`, written without any division by
`j(τ)−j(z)`. -/
def UpsilonMinusClear (d : ℕ) (τ z : ℍ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let jτ := jInvariantFun τ
  let jz := jInvariantFun z
  let J := jτ - jz
  if d = 8 then
    ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ •
      (PiMatDelta ![4, 2, 0] τ *
        !![-2 * c1728, 0, 0; 0, 1, -1; 0, c1728 - jτ, jτ] *
        PiMat ![10, 8, 6] z)
  else if d = 24 then
    ((2 : ℂ) * c1728 * (Real.pi : ℂ))⁻¹ •
      (PiMatDelta ![12, 10, 8] τ *
        !![-2 * c1728, -2 * c1728 * J, 0;
           0, jτ + 2 * J, -1;
           0, c1728 - 2 * J - jτ, 1] *
        (DeltaFun z • PiMat ![2, 0, -2] z))
  else 0

/-- The cleared kernel `Δ(τ)Δ(z)^{e}(j(τ)−j(z)) K_+^{(d)}(τ,z)`, holomorphic in both
variables. -/
def KPlusClear (d : ℕ) (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, phiVec τ i * UpsilonPlusClear d τ z i j * phitVec z j

/-- The cleared kernel `Δ(τ)Δ(z)^{e}(j(τ)−j(z)) K_-^{(d)}(τ,z)`, holomorphic in both
variables. -/
def KMinusClear (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, psiVec ℓ τ i * UpsilonMinusClear d τ z i j * psitVec ℓ z j

/-! ## Simple poles -/

/-- `HasSimplePoleWithResidue f z c` : the function `f` has at `z` a pole of order at most
one with residue `c`, i.e. `τ ↦ f τ - c/(τ - z)` is holomorphic at `z`. -/
def HasSimplePoleWithResidue (f : ℍ → ℂ) (z : ℍ) (c : ℂ) : Prop :=
  MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹) z

end Work.Kernels
