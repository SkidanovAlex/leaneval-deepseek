import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Submission.Work.BoseC3QAll.Q3T_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.Defs` — the objects of the proof of `eq:EstimateQ3Tilde1`

This module sets up the *interface* of the estimate `EstQ3oneA` (FS
`eq:EstimateQ3Tilde1`, `lem:EstimatesOnQ3-js`'s first piece): the shift
`Y_k` (FS's `c_k - b_k`), its adjoint `Y_k†`, and the leftover `R1` (FS's
`T₁(k)` plus the pieces of `T₂` that are not the square of the shift).

The starting point is the algebraic identity (`Q3T_split`, proved in the parent
directory)

  `Q3T = Q3oneT + Q3twoT + Q3threeT + Q3fourT`,

i.e. `Q₃⁽¹⁾ = (z/ℓ³)Σ_sΣ_{k∈P_H} f_L(s)Ŵ₁(k)q3Denom(s,k) •
     (ã_s†b_{s-k}b_k + β_{sk}ã_s†b_{k-s}†b_{-k}† + h.c.)`,
with `β_{sk} = α_kα_{s-k}`.

## The decomposition

Write `b_k† = bOpDag E.alpha k`, `b_k = bOp E.alpha k`, `Ã_s = ã_s + β_{sk}ã_{-s}†`.
The proof of `EstQ3oneA` runs on the identity

  `Q3oneT = Σ_{k∈P_H} (b_k†∘Y_k + Y_k†∘b_k) + R1`,

where the *shift* is

  `Y_k = (z/ℓ³) Σ_s γ_{sk} (b_{s-k}† ∘ Ã_s)`,   `γ_{sk} = f_L(s)Ŵ₁(k)q3Denom(s,k)`,

and the leftover is

  `R1 = (z/ℓ³) Σ_{s,k} γ_{sk}β_{sk} •
        ( κB_{sk}(b_k† + b_k) + κA_{sk}(b_{s-k}† + b_{s-k}) - κC_{sk}(ã_{-s}† + ã_{-s}) )`,

with the three *squeezed commutators* (each a multiple of the identity)

* `κA_{sk} = [ã_{-s}†, b_k†] = -α_k·ccrX(-s,-k)`,
* `κB_{sk} = [ã_{-s}†, b_{s-k}†] = -α_{s-k}·ccrX(-s,k-s)`,
* `κC_{sk} = [b_k†, b_{s-k}†] = (α_k - α_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k))`.

Every one of `κA, κB, κC` is small: `κA, κB` carry `α` (hence `𝓁`) and `ccrX`
(hence `η`), `κC` is the difference `α_k - α_{s-k}` (FS's `σ₂`, the one FS
estimate too roughly: by `alpha_lip` it is `≤ K₀𝓁K_Ha‖s‖`).

## The change of variables

The identity is FS's rewriting of `Q₃⁽¹⁾` "combined with the diagonalised
Bogoliubov Hamiltonian": the two `b†b†`/`bb` halves of `Q₃⁽¹⁾` are first
*reindexed* by `(s,k) ↦ (-s,-k)`, which is where `fL_even`, `W1_even`,
`hatChi_even`, `hatChiSq_even` and `alpha_even` are used (they make `γ` and `β`
invariant under the substitution).

## Contents

* `gA`, `bA` — the scalars `γ_{sk}`, `β_{sk}`.
* `kA`, `kB`, `kC` — the three squeezed commutator scalars.
* `cD` — the kinetic reserve weight `(1-𝓁²)𝒟_k`.
* `shift`, `shiftDag`, `R1` — FS's `Y_k`, `Y_k†` and the leftover.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `γ_{sk} = f_L(s)Ŵ₁(k)q3Denom(s,k)`, the weight of the `(s,k)` summand of `Q₃⁽¹⁾`
(FS `eq:CentralEstimateOfQ31`). -/
def gA (E : Q3Env Mode) (s k : Mode) : ℝ := E.fL s * E.W1 k * E.q3Denom s k

/-- `β_{sk} = α_kα_{s-k}`, the coefficient of the `b†b†`/`bb` half. -/
def bA (E : Q3Env Mode) (s k : Mode) : ℝ := E.alpha k * E.alpha (s - k)

variable {F : FockData Mode}

/-- `κA_{sk} = [ã_{-s}†, b_k†] = -α_k·ccrX(-s,-k)`. -/
def kA (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : ℝ :=
  - E.alpha k * T.ccrX (-s) (-k)

/-- `κB_{sk} = [ã_{-s}†, b_{s-k}†] = -α_{s-k}·ccrX(-s,k-s)`. -/
def kB (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : ℝ :=
  - E.alpha (s - k) * T.ccrX (-s) (k - s)

/-- `κC_{sk} = [b_k†, b_{s-k}†] = (α_k - α_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k))` (FS `σ₂`). -/
def kC (E : Q3Env Mode) (s k : Mode) : ℝ :=
  (E.alpha k - E.alpha (s - k)) * (E.hatChiSq s - E.hatChi k * E.hatChi (s - k))

/-- The kinetic reserve weight of the mode `k`: `(1-𝓁²)𝒟_k`. -/
def cD (E : Q3Env Mode) (k : Mode) : ℝ := (1 - E.lille ^ 2) * E.D k

/-- `Ã_s = ã_s + β_{sk}ã_{-s}†`: the combination the shift `Y_k` carries. -/
def Atil (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  T.ta s + (bA E s k) • T.taDag (-s)

/-- The adjoint `Ã_s† = ã_s† + β_{sk}ã_{-s}` (written out: the chapter has no
`†` operation on linear maps). -/
def AtilDag (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  T.taDag s + (bA E s k) • T.ta (-s)

/-- **FS's shift `Y_k`**: `(z/ℓ³)Σ_s γ_{sk}b_{s-k}†Ã_s`. -/
def shift (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode,
    (gA E s k) • (F.bOpDag E.alpha (s - k) ∘ₗ Atil F T E s k)

/-- **The adjoint of the shift**: `(z/ℓ³)Σ_s γ_{sk}Ã_s†b_{s-k}`. -/
def shiftDag (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode,
    (gA E s k) • (AtilDag F T E s k ∘ₗ F.bOp E.alpha (s - k))

/-- **The leftover of the decomposition** (FS's `T₁(k)` and the comm part of
`T₂`): `(z/ℓ³)Σ_{s,k}γ_{sk}β_{sk}(κB_{sk}(b_k†+b_k) + κA_{sk}(b_{s-k}†+b_{s-k})
- κC_{sk}(ã_{-s}†+ã_{-s}))`. -/
def R1 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  (E.z / E.ell ^ 3) • ∑ s ∈ excited Mode, ∑ k ∈ F.PHset E,
    (gA E s k * bA E s k) •
      ( (kB T E s k) • (F.bOpDag E.alpha k + F.bOp E.alpha k)
        + (kA T E s k) • (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))
        - (kC E s k) • (T.taDag (-s) + T.ta (-s)) )

/-- `ã_s†b_{s-k}b_k` (FS `Q₃⁽¹⁾`, first word). -/
def Q1a (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  T.taDag s ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)

/-- `ã_s†b_{k-s}†b_{-k}†` (FS `Q₃⁽¹⁾`, `b†b†` word). -/
def Q1b (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  T.taDag s ∘ₗ (F.bOpDag E.alpha (k - s) ∘ₗ F.bOpDag E.alpha (-k))

/-- `b_k†b_{s-k}†ã_s` (the adjoint word of `Q1a`). -/
def Q1aDag (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.ta s)

/-- `b_{-k}b_{k-s}ã_s` (the adjoint word of `Q1b`). -/
def Q1bDag (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOp E.alpha (-k) ∘ₗ (F.bOp E.alpha (k - s) ∘ₗ T.ta s)

/-- `b_k†b_{s-k}†ã_{-s}†`: the `β`-part of `b_k†Y_k`. -/
def S1 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag E.alpha k ∘ₗ (F.bOpDag E.alpha (s - k) ∘ₗ T.taDag (-s))

/-- `ã_{-s}b_{s-k}b_k`: the `β`-part of `Y_k†b_k`. -/
def S2 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s k : Mode) : F.H →ₗ[ℝ] F.H :=
  T.ta (-s) ∘ₗ (F.bOp E.alpha (s - k) ∘ₗ F.bOp E.alpha k)

end Est1

end Work.BoseC3QAll
