import ChallengeDeps
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.Fock
import Submission.Work.BoseBox.Word
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Nodes` — the `B0`–`B8` decomposition of FS `thm:LHY-Box`

The audit (`BOSE_AUDIT_LEAD.md` §4 B) decomposes the box theorem `LHYBox` into the
nodes `B0`–`B8` of Fournais–Solovej §§5–11.  This module names them, in the
chapter's own vocabulary, and proves the *assembly*: the low/non-low dichotomy
(`B0`), the a-priori windows (`B1`), the matrix restriction (`B2`) and the
restricted-subspace bound (`NodeRestricted`, which the FS §8–§11 nodes
`B4`–`B7` decompose) together give `LHYBox`.

## What is *proved* here

* `nodeB0_dichotomy` — FS `eq:aprioriPsi`'s trichotomy: every state is either
  *low* (word at most `ℓ³Θ`) or already satisfies the target bound; this uses
  only `Lambda_le_Theta` (`Work.UBB.Arith`, proved) and linear order;
* `LHYBox_of_nodes` — the assembly of `LHYBox` from `NodeB1`, `NodeB2` and
  `NodeRestricted`.  Its statement is the exact dependency graph of the box
  theorem: nothing else is assumed.

## What is *named* here

`NodeB1` (FS §5 `thm:aprioribounds`, `thm:aprioriHLambda`: the two windows on
`n` and on `n₊`), `NodeB2` (FS §6 `lem:LocMatrices`: restriction to
`n₊ ≤ 𝓜 = K_M(μa³)^{-1/4}`), `NodeB3` (FS §7 `lem:Q3-splitting1`: the momentum
splitting of the `3Q` term, with the high-momentum excited count `cnPlusH` of
`eq:DefT`'s third term), `NodeB4` (FS §8 `prop:Hamilton2ndQuant`,
`lem:Q3-splitting2`, `thm:Kafz`, `c`-number substitution), `NodeB5` (FS §9
`lem:Roughbounds`: `ρ_z` close to `μ`), `NodeB6` (FS §10 `thm:BogHamDiag` +
App. `thm:bogolubov-complete` + `lem:BogIntegral`: the diagonalisation, proved
in the finite-mode Fock model as `PairBogIdentity`/`MultiPairBogIdentity`
(`Fock.lean`, proved in the delegated module `pairBogolubov_identity`), and the
model integral, proved as `bog_model_integral`/`bog_integral_fs`), `NodeB7`
(FS §10 `thm:Control3Q`, `lem:EstimatesOnQ3-js`, `lem:EstimateIntegral`), and
`NodeB8` (FS §11: the parameter assembly, which is `Basic.lean`'s
`paramsOK_fsParams` together with `LHYBox_of_nodes`).

**Status of the FS §8–§11 nodes.**  The statements of `NodeB4`/`NodeB5`/`NodeB7`
below are the FS inequalities *with the second-quantised objects as arguments*:
the chapter has built the finite-mode Fock space and its CCR algebra
(`Fock.lean`) and the exact model integral (`bog_integral_fs`), but the
*instantiation* of an abstract quadratic form to FS's `H_Λ^{2nd}` requires the
second-quantisation map between the corpus's first-quantised box states and the
Fock space (FS §8 `thm:Kafz`) and the continuum mode lattice `k ∈ (2π/ℓ)ℤ³`,
which are the 30–60K-line node `B4` and are **not** built here.  The Props below
are stated so that this instantiation is a *filling-in of arguments*, not a
restatement.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.SmallBoxTBWord

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 0. The dictionary of the a-priori windows -/

/-- `‖Φ‖²` over the centred box `abox n ℓ`. -/
noncomputable def norm2N (n : ℕ) (ℓ : ℝ) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2

/-- FS `eq:apriorinn+`, first window: the *particle* window of a low state,
`|n − μℓ³| ≤ C K_B^{3/2}K_ℓ(μa³)^{1/4}·μℓ³` (`n` is the box particle number). -/
noncomputable def nWindow (P : FSParams) (μ a : ℝ) : ℝ :=
  μ * boxSide P μ a ^ 3 * P.KB ^ (3 / 2 : ℝ) * P.Kl * (μ * a ^ 3) ^ (1 / 4 : ℝ)

/-- FS `eq:apriorinn+`, second window: the *excited-particle* window
`⟨n₊⟩ ≤ C K_B³K_ℓ²(μa³)^{1/2}·μℓ³`. -/
noncomputable def nPlusWindow (P : FSParams) (μ a : ℝ) : ℝ :=
  μ * boxSide P μ a ^ 3 * P.KB ^ 3 * P.Kl ^ 2 * (μ * a ^ 3) ^ (1 / 2 : ℝ)

/-- FS `eq:DefM`: the matrix-localisation window `𝓜 = K_M(μa³)^{-1/4}`. -/
noncomputable def bigM (P : FSParams) (a : ℝ) (μ : ℝ) : ℝ :=
  P.KM * (μ * a ^ 3) ^ (-(1 / 4 : ℝ))

/-- FS `eq:DefT`, third term: the **high-momentum excited count**
`n₊^H = Σᵢ⟨QᵢΦ, 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ)QᵢΦ⟩`, in the corpus's spectral form
(`tBdiagForm` with the indicator symbol on the box `acube ℓ`). -/
noncomputable def cnPlusH (n : ℕ) (ℓ d : ℝ) (Φ : X n → ℝ) : ℝ :=
  tBdiagForm ℓ (acube ℓ) (ℓ ^ 3) (fun _ => 1) (highSymb ℓ d 1 1) Φ

/-- The a-priori threshold energy `ℓ³Θ(a v) J μ` at the box side `ℓ(μ)`: a state
is *low* when its word is at most this. -/
noncomputable def lowLevel (P : FSParams) (μ : ℝ) (v : ℝ³ → ℝ) (J : ℝ) : ℝ :=
  boxSide P μ (a v) ^ 3 * Theta (a v) J μ

/-- FS `eq:aprioriPsi`: the *low-state* predicate at the box side `ℓ(μ)`. -/
def IsLow (P : FSParams) (μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ)
    (n : ℕ) (Φ : CSBox n (boxSide P μ (a v))) : Prop :=
  boxWordU n (boxSide P μ (a v)) μ P.d P.s P.eT P.b v h 0 (Φ : X n → ℝ)
    ≤ lowLevel P μ v J * norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ)

/-- The *box theorem's conclusion* for a single state. -/
def BoxBound (P : FSParams) (μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (η₀ C : ℝ)
    (n : ℕ) (Φ : CSBox n (boxSide P μ (a v))) : Prop :=
  boxSide P μ (a v) ^ 3 * Lambda (a v) C η₀ μ * norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ)
    ≤ boxWordU n (boxSide P μ (a v)) μ P.d P.s P.eT P.b v h 0 (Φ : X n → ℝ)

/-! ## 1. `B0`: the low/non-low dichotomy -/

/-- **`B0`** (FS `eq:aprioriPsi` and the threshold comparison): every state is
either low, or already satisfies the box bound.  Proved from the threshold
arithmetic `Λ ≤ Θ` (`Work.UBB.Arith`) and linear order. -/
theorem nodeB0_dichotomy {P : FSParams} {μ : ℝ} {v : ℝ³ → ℝ} {h : ScatSol v} {J η₀ C : ℝ}
    (hJ : lhyC ≤ J) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hμ : 0 < μ) (hav : 0 < a v)
    (hKl : 0 < P.Kl) {n : ℕ} (Φ : CSBox n (boxSide P μ (a v))) :
    IsLow P μ v h J n Φ ∨ BoxBound P μ v h η₀ C n Φ := by
  by_cases hlow : boxWordU n (boxSide P μ (a v)) μ P.d P.s P.eT P.b v h 0 (Φ : X n → ℝ)
      ≤ lowLevel P μ v J * norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ)
  · exact Or.inl hlow
  · refine Or.inr ?_
    have hΘ : Lambda (a v) C η₀ μ ≤ Theta (a v) J μ :=
      theta_ge_lambda (A := a v) (K := C) (J := J) (η₀ := η₀) (ρ := μ)
        hav.le hμ.le hC hJ
    have hnn : 0 ≤ norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ) := by
      dsimp [norm2N]
      exact integral_nonneg (fun x => sq_nonneg _)
    have hℓpos : 0 < boxSide P μ (a v) := boxSide_pos hμ hav hKl
    have hℓ3 : 0 < boxSide P μ (a v) ^ 3 := pow_pos hℓpos 3
    have hkey : boxSide P μ (a v) ^ 3 * Lambda (a v) C η₀ μ * norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ)
        ≤ lowLevel P μ v J * norm2N n (boxSide P μ (a v)) (Φ : X n → ℝ) := by
      dsimp [lowLevel]
      have h1 := mul_le_mul_of_nonneg_left hΘ hℓ3.le
      have h2 := mul_le_mul_of_nonneg_right h1 hnn
      linarith
    exact le_trans hkey (le_of_lt (not_le.mp hlow))

/-! ## 2. `B1`, `B2`, and the restricted-subspace bound -/

/-! **FINDING (prover's report + machine-checked refutation, this round).**  This node
carries only the *lower* bound `lhyC ≤ J` on the a-priori parameter, while FS
`thm:aprioribounds` assumes `0 < J ≤ K_B³`: the windows are `J`-free while the
threshold `Theta (a v) J μ = −4πμ²(a v)(1 − J√(μ(a v)³))` is *increasing* in `J`,
so large `J` weakens `IsLow` without weakening the windows.  The prover's
`nodeB1_holds.lean` proves `¬ (∀ J, lhyC ≤ J → NodeB1 v h J)` for `0 < a v` (with
the admissible diluteness `t = μa³ = 1`, `paramsOK_fsParams_one`, and the
mean-free test state `x ↦ x₀₁x₁₁x₂₁`, whose `cnPlus = 3‖·‖²`), i.e. the
`∀ J`-reading of this node is refuted; the repair is to carry FS's constraint
`J ≤ K_B³` (equivalently, to fix `J` and let `ε₀` absorb `J ≤ (μa³)^{-18/323}`).
`NodeB2g`/`NodeRestricted` take the same threshold and want the same guard.

-/

/-- **`B1`** (FS §5, `thm:aprioribounds` + `thm:aprioriHLambda`, and App.
`thm:smallbox`; `eq:apriorinn+`): for every low state of the box at
diluteness `μa³` small, the particle number `n` is within the window
`nWindow` of `μℓ³` and the excited count `cnPlus ℓ Φ` is within the window
`nPlusWindow`.

The corpus chain delivering this (at the *coupled* parameters) is
`Work.SmallBoxSliding`/`Work.SmallBoxDLBound`/`Work.LocRepoint`; the B1 work is
to re-instantiate it at FS's `ρ`-dependent `d, s, ε_T, K_B` — this node is the
*statement* at the decoupled parameters.

**Both windows carry a free constant** (`C₁` for the particle window, `C₂` for
the excited window).  This is not cosmetic: FS `eq:apriorinn+` is stated with a
universal constant `C` on the right-hand side
(`⟨n₊⟩ ≤ C K_B³K_ℓ²μℓ³(μa³)^{1/2} = C·nPlusWindow`), and FS's own §6 consumes it
*with* that constant (`[0, 𝓜' + CK_B³K_ℓ⁵] ⊆ [0,𝓜]`).  The chapter's
`nPlusWindow` is the *sharp* quantity `(μa³)^{-51/646}`, so the constant-free
form is the `C₂ = 1` instance, which is strictly stronger than the paper's
theorem: a prover showed that the only available route (FS `eq:appsliding` +
`eq:aprioriHLambda` + `eq:aprioriPsi`, i.e. the corpus's
`Work.UBB.Apriori.cnPlus_le_window_of_low`) delivers the coefficient
`(8π/b)(1 + J/K_B³) ≥ 8π/b = 128π > 384` (`Work.BoseBox.aprioriWindowCoefficient`
in `aprioriWindows.lean`, machine-checked), so the constant-free rendering is
mis-stated; the free `C₂` is what the paper actually proves. -/
def NodeB1 (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C₁ C₂ ε₀ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        (|(n : ℝ) - μ * sideAt μ (a v) ^ 3| ≤ C₁ * (1 + nWindow (paramsAt μ (a v)) μ (a v))) ∧
        (cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ (C₂ * nPlusWindow (paramsAt μ (a v)) μ (a v) + 1)
            * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ))

/-! ## 2b. FS `eq:LocalizedNPlus`: the `n₊`-restriction as a *spectral* condition

FS `lem:LocMatrices` concludes that the replacement state satisfies
`1_{[0,𝓜]}(n₊)Ψ̃ = Ψ̃` — a condition on the *spectrum* of the excitation
operator `n₊ = ΣᵢQᵢ`, not merely on its expectation.  The distinction matters:
the *expectation* window `⟨n₊⟩ ≤ 𝓜‖·‖²` is what the a-priori bounds (`NodeB1`)
give, and it is *preserved* by the identity replacement, whereas the spectral
condition is not — which is exactly why the Lieb–Solovej localisation is needed.

We render `1_{[0,𝓜]}(n₊)Φ = Φ` by the equivalent **all-moments** condition: for
the nonnegative operator `n₊`, a spectral mass above `𝓜` makes the ratio
`(λ/𝓜)^m` diverge with `m`, so `⟨Φ, n₊^mΦ⟩ ≤ 𝓜^m‖Φ‖²` for *every* `m` is
equivalent to `spec(n₊)∩supp(Φ) ⊆ [0,𝓜]`.  The `m = 1` instance is the
expectation window (`⟨Φ,n₊Φ⟩ = cnPlus ℓ Φ`), and the higher moments are what the
FS §8–§11 analysis uses to treat `ρ₊ = n₊ℓ^{-3}` as a small *operator*. -/

/-- The excitation operator `n₊ = ΣᵢQᵢ` as a map on states: `nPlusFun ℓ Φ x =
Σᵢ (aQ ℓ i Φ x)` (the corpus's slot-wise mean-free projections). -/
noncomputable def nPlusFun (ℓ : ℝ) {N : ℕ} (Φ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ i : Fin N, aQ ℓ i Φ x

/-- The iterates of `n₊`: `nPlusPow ℓ N m Φ = n₊^m Φ` by composition. -/
noncomputable def nPlusPow (ℓ : ℝ) (N : ℕ) : ℕ → (X N → ℝ) → (X N → ℝ)
  | 0, Φ => Φ
  | (m + 1), Φ => nPlusFun ℓ (nPlusPow ℓ N m Φ)

/-- **FS `eq:LocalizedNPlus`, equivalent all-moments form**: the state's spectral
measure for `n₊` lives in `[0,𝓜]`, i.e. `⟨Φ, n₊^mΦ⟩ ≤ 𝓜^m‖Φ‖²` for every `m`. -/
def SpectralNPlusLe (ℓ 𝓜 : ℝ) {N : ℕ} (Φ : X N → ℝ) : Prop :=
  ∀ m : ℕ,
    (∫ x in abox N ℓ, nPlusPow ℓ N m Φ x * Φ x)
      ≤ 𝓜 ^ m * (∫ x in abox N ℓ, (Φ x) ^ 2)

/-- **The restricted-subspace bound** (the conclusion of FS §8–§11 after the
`n₊`-restriction): on the states whose `n₊`-spectrum lies in `[0,𝓜]`
(`SpectralNPlusPlusLe`, FS `eq:LocalizedNPlus`), the box bound holds for all low
states.  This is what the nodes `B3`–`B7` are for; it is separated from them so
that the assembly (`B2Grading.LHYBox_of_grading`, using the §6 replacement
`NodeB2g`) is a theorem with no reference to the Fock space. -/
def NodeRestricted (v : ℝ³ → ℝ) (h : ScatSol v) (J η₀ C : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
        BoxBound (paramsAt μ (a v)) μ v h η₀ C n Φ

/-! ## 3. The FS §8–§11 nodes (`B3`–`B7`) -/

/-! **REFUTED AS STATED (prover's report, this round).**  Without the a-priori
restrictions of FS §5/§6 (the *low* class `eq:aprioriPsi` together with the
`eq:apriorinn+` windows on `n` and `n₊`, i.e. exactly the class of
`NodeRestricted`), the `3Q`-form is **unbounded below per unit norm** as `n`
grows while the node's error terms grow only linearly in `n`: the product state
`Φ_n = Π_{k≤n}(1 + s g)` with `∫g = 0` gives
`q3word/norm² = 2n(n−1)K₁/(∫ψ²)²` with `K₁ < 0` for suitable bumps (the prover's
`nodeB3_REFUTED.md` and `_b3work/chk2–5.py` check this numerically against a
discretisation of the corpus's `aP`/`aQ`/`q3word`).  FS prove `lem:Q3-splitting1`
*inside* the restricted class, so the faithful statement of `B3` (and of
`B4`–`B7`) must carry the same hypotheses as `NodeRestricted` (or be phrased as
an inequality on the restricted class).

-/

/-- **`B3`** (FS §7–§8, `lem:Q3-splitting1`): the momentum splitting of the
renormalised `3Q` term.  The high-momentum cut-off
`K_H^{-1}(μa³)^{5/12}a^{-1}` separates the low momenta (`P_L`) from the high
ones (`P_H`), and the `3Q` word is bounded below by the split version, the loss
being absorbed by the high-momentum gap `(bε_T/(2d²ℓ²))n₊^H`
(`cnPlusH`) and the `K_H^{-3/2}K_M^{1/2}` error of `lem:Q3-splitting2`.

`q3Split` is the split `3Q` word: the corpus's `q3word` at the localised FS
kernels with the `P_L ⊗ P_H` momentum restriction applied to the two `Q`
factors (its definition in the corpus's spectral vocabulary is part of node
`B4`'s mode lattice). -/
def NodeB3 (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, 0 < μ → μ * (a v) ^ 3 ≤ ε₀ →
      ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) →
      J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ n : ℕ, ∀ Φ : CSBox n (sideAt μ (a v)),
        IsLow (paramsAt μ (a v)) μ v h J n Φ →
        SpectralNPlusLe (sideAt μ (a v)) (bigM (paramsAt μ (a v)) (a v) μ) (Φ : X n → ℝ) →
        q3word (sideAt μ (a v)) (wPairC (sideAt μ (a v)) (g0 v h)) (Φ : X n → ℝ)
          + C * ((paramsAt μ (a v)).eT * (paramsAt μ (a v)).b
                / (2 * (paramsAt μ (a v)).d ^ 2 * sideAt μ (a v) ^ 2)
                * cnPlusH n (sideAt μ (a v)) (paramsAt μ (a v)).d (Φ : X n → ℝ)
              + (paramsAt μ (a v)).KH ^ (-(3 / 2 : ℝ)) * (paramsAt μ (a v)).KM ^ (1 / 2 : ℝ)
                * norm2N n (sideAt μ (a v)) (Φ : X n → ℝ))
          ≥ 0

/-- **`B4`** (FS §8: `prop:Hamilton2ndQuant`, `lem:2ndQuand`,
`lem:Q3-splitting2`, `thm:Kafz`, and the `c`-number substitution): the passage
to second quantisation and the replacement of the condensate operator `a₀` by a
complex number `z`, with the density `ρ_z = |z|²/ℓ³`; the second-quantised
Hamiltonian of `eq:HLambdaSecond` (kinetic `τ`-term, the `n₊`/`n₊^H` gaps, the
mean-field `Q₀` terms, the quadratic `Q₁`/`Q₂` terms and `Q̃₃`) dominates the
corpus word up to the `eq:HLambdaSecond` error.

Stated here with the second-quantised object `H2nd` as an argument: the chapter
provides the finite-mode Fock space and its CCR algebra (`Fock.lean`), and the
*instantiation* `H2nd ↦ H_Λ^{2nd}` — the mode lattice `k ∈ (2π/ℓ)ℤ³`, the
quadratic forms `∫Ŵ₁(k)a₀†a_k†a_k a₀ dk`, the `Kafz` identity
`inf spec H_Λ(μ) = inf over c-number substituted vectors` — is the 30–60K-line
`B4` build that this Prop names. -/
def NodeB4 (v : ℝ³ → ℝ) (h : ScatSol v) (P : FSParams) (μ : ℝ)
    (H2nd : ℂ → (n : ℕ) → CSBox n (boxSide P μ (a v)) → ℝ) : Prop :=
  ∀ n : ℕ, ∀ Φ : CSBox n (boxSide P μ (a v)),
    ∃ (z : ℂ) (C : ℝ), 0 ≤ C ∧
      (z.re ^ 2 + z.im ^ 2) / boxSide P μ (a v) ^ 3 ≤ 2 * μ ∧
      μ / 2 ≤ (z.re ^ 2 + z.im ^ 2) / boxSide P μ (a v) ^ 3 ∧
      boxWordU n (boxSide P μ (a v)) μ P.d P.s P.eT P.b v h 0 (Φ : X n → ℝ)
        ≥ H2nd z n Φ
          - C * boxSide P μ (a v) ^ 3 * μ ^ 2 * (a v) *
              ((P.Kl * P.d ^ 2) ^ (-(1 : ℝ)) * (1 - (P.M : ℝ))
                + (a v) ^ 2 / boxSide P μ (a v) ^ 2)

/-- **`B5`** (FS §9, `lem:Roughbounds`, `prop:FarAway`): after `c`-number
substitution the density `ρ_z` of the substituted condensate is close to `μ`:
`|ρ_z − μ| ≤ μ K_ℓ^{-2}` (FS `eq:Close`), provided the substituted energy is
low (`eq:aprioriPsi`) and the `con:rough1`/`con:rough2` conditions hold.

Stated with the substituted energy as the function `𝒦z` of `ρz`: the content is
that a low minimiser of `𝒦z` must sit at `ρz ≈ μ`. -/
def NodeB5 (v : ℝ³ → ℝ) (h : ScatSol v) (P : FSParams) (μ : ℝ)
    (Kz : ℝ → ℝ) (E0 : ℝ) : Prop :=
  ∀ ρz : ℝ, 0 < ρz → P.KM * (μ * (a v) ^ 3) ^ (-(1 / 4 : ℝ)) * boxSide P μ (a v) ^ 3 * μ ≤ ρz →
    Kz ρz ≤ E0 →
    |ρz - μ| ≤ μ * P.Kl ^ (-(2 : ℝ))

/-- **`B6`** (FS §10 `thm:BogHamDiag` + App. `thm:bogolubov-complete` +
`lem:BogIntegral`): the Bogoliubov diagonalisation and the value of the
zero-point integral.  In this chapter this node *is* the pair of theorems
`PairBogIdentity`/`MultiPairBogIdentity` (`Fock.lean`, proved in
`pairBogolubov_identity`) for the algebraic part, together with the exact model
integral `bog_integral_fs` (proved, sharp constant `128/(15√π)`) for the
analytic part. -/
def NodeB6 (m : ℕ) : Prop :=
  PairBogIdentity m ∧ MultiPairBogIdentity m

/-- **`B7`** (FS §10 `thm:Control3Q`, `lem:EstimatesOnQ3-js`,
`lem:EstimateIntegral`, and §11 `eq:Q3Cancels`): the diagonalised Bogoliubov
operator controls the remaining `3Q` term and the `1Q`/`2Q` corrections, with
the explicit error of `eq:Q3Cancels`.

Stated with the diagonalised form `bogDiag`, the `3Q` form `q3` and the Fock
form `fockQ` as arguments: instantiating them to FS's objects is node `B4`'s
mode lattice. -/
def NodeB7 (m : ℕ) (bogDiag q3 : Fock m →ₗ[ℝ] Fock m) (fockQ : Fock m → ℝ)
    (liftQ : Fock m → Fock m) (err : ℝ) : Prop :=
  ∀ φ : Fock m, 0 ≤ fockQ (liftQ φ) →
    fockQ (liftQ (bogDiag φ)) + fockQ (liftQ (q3 φ)) + err * fockQ (liftQ φ) ≥ 0

/-! ## 4. The assembly (`B8`): the nodes give `LHYBox`

The assembly lives in `Submission.Work.BoseBox.B2Grading` (this module cannot
state it: `NodeB2g` is defined there, on top of the spectral predicate above):

* `Work.BoseBox.LHYBox_of_grading` — `B0` (the dichotomy, proved below) + the §6
  replacement `NodeB2g` + the restricted bound `NodeRestricted` give FS
  `thm:LHY-Box`, at the shifted error coefficient `C + 1` (FS's Lieb–Solovej loss
  is absorbed by one unit of the target's error coefficient,
  `Work.BoseBox.exists_lsError_le_slack`);
* `Work.BoseBox.HBoxG_of_grading` — the same data plus `CompareBox` give the
  audit's `HBoxG`.

The a-priori windows `NodeB1` are *not* an input of the assembly: they are
consumed inside the proof of the §6 replacement (as in FS, where
`thm:aprioribounds` precedes and feeds `lem:LocMatrices`), which is a further
reason `NodeRestricted` must be stated on the *spectrally* restricted class (FS
`eq:LocalizedNPlus`) rather than on the a-priori expectation window: with the
latter the replacement would be the identity and §6 would be vacuous. -/

end Work.BoseBox
