import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.FockDefs` — node `B7`'s Fock interface

This is the vocabulary of node `B7` of `BOSE_AUDIT_LEAD.md` §4, i.e. Fournais–Solovej
§10: `thm:Control3Q`, `lem:EstimatesOnQ3-js`, `lem:EstimateIntegral` — the
control of the cubic term `3Q`.

## The interface (what `B4` must supply)

FS §8 second-quantises the box Hamiltonian on the bosonic Fock space over
`L²(Λ)`; the *mode lattice* is `k ∈ (2π/ℓ)ℤ³` (so that `(2π)^{-3}ℓ³∫dk` is the
normalised sum over lattice points).  The whole of §10 uses only

* the mode set `Mode` (an additive group, so that FS's labels `-k` and `s-k`
  make sense) with a momentum *assignment* `kmom : Mode → ℝ³`, odd under
  negation (`kmom (-i) = -kmom i`): only `‖kmom i‖` (the momentum regions
  `P_L, P_H`) and the parity are ever used,
* the annihilation/creation operators `a i`, `a i†`,
* the commutation package `[a_i,a_j] = [a_i†,a_j†] = 0` and, the *box*
  commutator of FS `eq:Commutator_general`,

      `[a_k, a_{k'}†] = ccrK k k' := χ̂²((k-k')ℓ) - χ̂(kℓ)·χ̂(k'ℓ)`

  (in infinite volume `ccrK` is the delta `ℓ⁻³δ(k-k')`; on a box of side `ℓ`
  it is the explicit decaying kernel above — this is what makes FS
  `eq:1Q-integral2` a genuine term),
* the Fock inner product `bp`, with `a_i†` the adjoint of `a_i` (so that
  `⟨Φ, a_i†a_iΦ⟩ = ‖a_iΦ‖² ≥ 0`) and positivity/definiteness.

`FockData` collects exactly this.  Every statement of the chapter is made
*relative to* a `FockData`, i.e. it takes it as a hypothesis: filling in `B4`'s
second-quantisation map and mode lattice instantiates the chapter without
restating anything.

## Contents

* `ccrKernel` — FS `eq:Commutator_general`'s kernel.
* `FockData` — the interface (algebra + form + momentum) and its fields.
* `FockData.nOp`, `nPlus`, `bOp`, `bOpDag`, `bNumOp`, `PH`, `PL`, `SpectLe`,
  `regionSum`, `dNumOp` — the operators, the momentum regions and the spectral
  window of FS §7–§10.

The API (Cauchy–Schwarz, number-operator bounds, squeezed modes and their
commutators) is in `Work.BoseB7.FockAPI`; the exact `3Q` splitting algebra is in
`Work.BoseB7.Q3Algebra`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- FS `eq:Commutator_general`: the commutator kernel of the second-quantised
operators on a box of side `ell`,

  `[a_k, a_{k'}†] = ℓ⁻³⟨Q(e^{ikx}χ_Λ), Q(e^{ik'x}χ_Λ)⟩ = χ̂²((k-k')ℓ) - χ̂(kℓ)χ̂(k'ℓ)`.

`hatChiSq` is the (normalised) Fourier transform of `χ_Λ²`, `hatChi` that of
`χ_Λ` (so that `hatChiSq 0 = hatChi 0 = 1`). -/
def ccrKernel (ell : ℝ) (hatChiSq hatChi : ℝ³ → ℝ) (k k' : ℝ³) : ℝ :=
  hatChiSq (ell • (k - k')) - hatChi (ell • k) * hatChi (ell • k')

/-- **The `B4` Fock interface**: a bosonic mode system with the FS box
commutator and a Fock inner product.  This is the hypothesis against which every
statement of the `B7` chapter is made; `B4`'s second quantisation of
`H_Λ^{2nd}` is what instantiates it.

The `Mode` index is an additive group (FS's momentum lattice, so that `k ↦ -k`
and `(s,k) ↦ s-k` are available), with the momentum as an additive map
`kmom : Mode →+ ℝ³`. -/
structure FockData (Mode : Type*) [AddCommGroup Mode] [Fintype Mode] where
  /-- The carrier of the Fock space. -/
  H : Type*
  [instAddCommGroup : AddCommGroup H]
  [instModule : Module ℝ H]
  /-- The momentum of a mode (FS's `k`).  It is *data*, not a group
  homomorphism: in a periodic box the momentum labels live on the dual torus, and
  only the values `‖kmom i‖` (and the parity `kmom (-i) = -kmom i`) are ever
  used. -/
  kmom : Mode → ℝ³
  /-- The momentum is odd under negation of the mode (`kmom (-i) = -kmom i`), so
  that FS's momentum regions `P_L`, `P_H` are invariant under `k ↦ -k`. -/
  kmom_neg : ∀ i : Mode, kmom (-i) = -kmom i
  /-- The annihilation operator `a_k`. -/
  a : Mode → H →ₗ[ℝ] H
  /-- The creation operator `a_k†`. -/
  aDag : Mode → H →ₗ[ℝ] H
  /-- `[a_i, a_j] = 0`. -/
  ann_comm : ∀ i j : Mode, a i ∘ₗ a j = a j ∘ₗ a i
  /-- `[a_i†, a_j†] = 0`. -/
  cre_comm : ∀ i j : Mode, aDag i ∘ₗ aDag j = aDag j ∘ₗ aDag i
  /-- FS `eq:Commutator_general`: the values of `[a_i, a_j†]` (a scalar). -/
  ccrK : Mode → Mode → ℝ
  /-- FS `eq:Commutator_general`: `[a_i, a_j†] = ccrK i j` at the operator level. -/
  ccr : ∀ i j : Mode, a i ∘ₗ aDag j = aDag j ∘ₗ a i + (ccrK i j) • 1
  /-- The Fock inner product (`⟨Φ,Ψ⟩`). -/
  bp : H →ₗ[ℝ] H →ₗ[ℝ] ℝ
  /-- `bp` is symmetric. -/
  bp_symm : ∀ f g : H, bp f g = bp g f
  /-- `bp` is positive semidefinite. -/
  bp_nonneg : ∀ f : H, 0 ≤ bp f f
  /-- `bp` is definite (the Fock norm is a norm). -/
  bp_def : ∀ f : H, bp f f = 0 → f = 0
  /-- `a_i†` is the adjoint of `a_i` (so that `⟨Φ, a_i†a_iΦ⟩ = ‖a_iΦ‖²`). -/
  aDag_adjoint : ∀ (i : Mode) (f g : H), bp (aDag i f) g = bp f (a i g)

attribute [instance] FockData.instAddCommGroup FockData.instModule

/-- The **excited modes**: every sum of the chapter runs over `excited Mode`,
because FS's `thm:Kafz` replaces `a₀` by the `c`-number `z` — the mode `0` is the
condensate and is never excited (`n₊ = Σ_{i ≠ 0} a_i†a_i`, FS `lem:2ndQuand`). -/
def excited (Mode : Type*) [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] :
    Finset Mode := Finset.univ.erase (0 : Mode)

namespace FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable (F : FockData Mode)

/-! ## 1. Modes, regions and the spectral window -/

/-- FS's high-momentum region `P_H = {|k| ≥ ½ K_H⁻¹ a⁻¹}` (the region of the
`3Q` term; the `½` is FS's). -/
def PH (KH a : ℝ) (i : Mode) : Prop := 1 / (2 * KH * a) ≤ ‖F.kmom i‖

/-- FS's low-momentum region `P_L = {|p| ≤ K_L√(μa)}`. -/
def PL (KL μ a : ℝ) (i : Mode) : Prop := ‖F.kmom i‖ ≤ KL * Real.sqrt (μ * a)

instance (KH a : ℝ) : DecidablePred (F.PH KH a) :=
  fun i => decidable_of_iff (1 / (2 * KH * a) ≤ ‖F.kmom i‖) Iff.rfl

instance (KL μ a : ℝ) : DecidablePred (F.PL KL μ a) :=
  fun i => decidable_of_iff (‖F.kmom i‖ ≤ KL * Real.sqrt (μ * a)) Iff.rfl

/-- A weighted sum over the *excited* modes of a region:
`regionSum R w op = Σ_{i ∈ R, i ≠ 0} w i • op i`, i.e. FS's
`(2π)^{-3}ℓ³∫_R ... dk` restricted to `Ran Q` (`thm:Kafz`). -/
def regionSum (R : Mode → Prop) [DecidablePred R] (w : Mode → ℝ)
    (op : Mode → F.H →ₗ[ℝ] F.H) : F.H →ₗ[ℝ] F.H :=
  ∑ i ∈ (excited Mode).filter R, (w i) • op i

/-! ## 2. The number operators -/

/-- The number operator of the mode `i`: `n_i = a_i†a_i`. -/
def nOp (i : Mode) : F.H →ₗ[ℝ] F.H := F.aDag i ∘ₗ F.a i

/-- The number of *excited* particles, `n₊ = Σ_{k ≠ 0} a_k†a_k` — in FS's
normalisation `(2π)^{-3}ℓ³∫ã_k†ã_k dk`, since one lattice point carries weight
`(2π/ℓ)³·(2π)^{-3}ℓ³ = 1`.  The condensate mode `0` is excluded (`a_0` becomes
the `c`-number `z` in `thm:Kafz`). -/
def nPlus : F.H →ₗ[ℝ] F.H :=
  ∑ i ∈ excited Mode, F.nOp i

/-- **The spectral window of FS §6–§10** (`eq:LocalizedNPlus`): the state has at
most `M` excited particles, in the `n₊`-quadratic-form sense
`⟨Φ, n₊Φ⟩ ≤ 𝓜 ‖Φ‖²` used by every estimate of §10. -/
def SpectLe (M : ℝ) (f : F.H) : Prop := F.bp (F.nPlus f) f ≤ M * F.bp f f


/-! ## 3. The squeezed modes `b_k` of FS `eq:Defb_k` -/

/-- FS `eq:Defb_k` without the `c`-number shift: `b_k = a_k + α_k a_{-k}†`.
(The shift `c_k` is the linear-term bookkeeping of `thm:BogHamDiag`; the
estimates of `lem:EstimatesOnQ3-js` are stated for this `b`, as in their
proofs.) -/
def bOp (α : Mode → ℝ) (i : Mode) : F.H →ₗ[ℝ] F.H := F.a i + (α i) • F.aDag (-i)

/-- The adjoint of `b_k = a_k + α_k a_{-k}†`: `b_k† = a_k† + α_k a_{-k}`.  The
adjointness `bp (bOpDag α k f) g = bp f (bOp α k g)` holds for *every* `α`
(`a_{k†}` is the adjoint of `a_k` and `a_{-k}` of `a_{-k}†`); evenness of `α` is
*not* needed for it (it is needed only for FS's rewriting of `α_{-k}`). -/
def bOpDag (α : Mode → ℝ) (i : Mode) : F.H →ₗ[ℝ] F.H := F.aDag i + (α i) • F.a (-i)

/-- `b_k†b_k` — the positive operator of FS `thm:BogHamDiag`'s diagonal form. -/
def bNumOp (α : Mode → ℝ) (i : Mode) : F.H →ₗ[ℝ] F.H := F.bOpDag α i ∘ₗ F.bOp α i

/-- FS `eq:Defb_k` *with* the `c`-number shift `c_k`. -/
def bOpShift (α c : Mode → ℝ) (i : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOp α i + (c i) • (1 : F.H →ₗ[ℝ] F.H)

/-- FS `thm:BogHamDiag`'s diagonalised quadratic operator restricted to a region:
`dNumOp R D α = (2π)^{-3}ℓ³∫_R D_k b_k†b_k dk`. -/
def dNumOp (R : Mode → Prop) [DecidablePred R] (D α : Mode → ℝ) : F.H →ₗ[ℝ] F.H :=
  F.regionSum R D (F.bNumOp α)

end FockData

end Work.BoseB7
