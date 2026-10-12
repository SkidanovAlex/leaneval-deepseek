import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.UBBInputs4.APrioriRoute
import Submission.Work.UBBInputs4.WindowNeu_embNeu_le_boxSq
import Submission.Work.UBBInputs4.cnPlus_eq_qform_nPlus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs5.Defs` — round 5: the residuals of the three clauses and of §9–11

**Assignment (round 5).** `Submission/Work/UBBInputs4/README.md` §2 closes the end-to-end
`Work.UBBInputs4.hpres_of_gradingNeu` at the *shortest* hypothesis list

    NPlusGradingNeu  v h J W ε₀ η₀        (FS §7 steps (2)–(5))
    BogoliubovWindowedNeu v h J W ε₀ η₀   (FS §9–11, window only)

and §3 decomposes `NPlusGradingNeu` into the three separately attackable clauses
`GradingBlocksNeu` (§7 (2)+(3)), `GradingDvNeu` (§7 (4) = `eq:dvapriori`) and
`GradingRecombNeu` (§7 (5)).  Round 5 attacks *those clauses*, i.e. the two residuals, and
this file fixes the vocabulary of the attack.

## The four residuals of round 5

| round-4 hypothesis | round-5 residual here | the missing mathematics |
|---|---|---|
| `GradingBlocksNeu` | **`SectorModelNeu`** | FS §7 (2)+(3): exhibit the box Hamiltonian as a self-adjoint operator `H` on a Hilbert space with a self-adjoint resolution of unity `E i = 1_{n₊=i}` with respect to which `H` is *band ≤ 2*; the block matrix `blk`, its matrix-support band property, its Hermiticity, its unit sector-norm vector `sec` and the energy identity are then **proved** (`Reduce.Blocks`, `SectorModel/*`) |
| `GradingDvNeu` | **`GradingDvSupNeu`** | FS §7 (4) `eq:dvapriori` split over the four *directed* expectations `dSup A n ψ (±1), dSup A n ψ (±2)`, each of which is in the sector model the expectation `⟨1_{n₊=i}Ψ, H_Λ(μ) 1_{n₊=i±k}Ψ⟩` of an explicit `Q`-word (the corpus's `Submission.QCrossD`, `Work.QCrossQuarter{,D2}` estimates), `SectorModel.dSup_blk_eq` |
| `GradingRecombNeu` | **`RecombEnergyNeu` + `RecombWindowNeu`** | FS §7 (5): the recombined state `Ψ̃ = ‖φ̃‖⁻¹Σᵢφ̃ᵢ‖1_{n₊=i}Ψ‖⁻¹1_{n₊=i}Ψ` with the energy bound (the construction, `Recomb.Energy`) and FS's *a-priori* argument turning that bound into the `n₊`-window (`eq:apriorinn+` on `Ψ̃`, `RecombWindowNeu`, `Reduce.Recomb`) |
| `BogoliubovWindowedNeu` | **the `bogQuad`/`bogLhy`/`bogErr` form** | FS §9–11: unchanged as a residual, but rewritten in the paper's own three terms — the mean-field term `bogQuad`, the LHY gain `bogLhy` (the `lem:BogIntegral` evaluation `lhyC = 128/(15√π)`), and the error `bogErr` (`Bogoliubov/Lambda`), so the residual is *pinned* rather than merely named |

Everything in this directory is `sorry`-free; `README.md` carries the per-file ledger and the
clause-by-clause roadmap.

## The finding of round 5

The two round-4 residuals are **not** further reducible to anything the corpus already
contains: `SectorModelNeu` is exactly *"FS's `eq:Def_HB` read at the corpus objects"* (the
localised Hamiltonian `H_Λ(μ)` as a self-adjoint band-`≤2` operator over the `n₊`-sectors,
with its normalised quadratic form equal to the shifted Rayleigh quotient), and the `Q`-word
expectations of `GradingDvSupNeu` are exactly FS's `thm:aprioribounds`.  What round 5 *does*
prove is everything between them: the sector model ⟹ the graded datum (the matrix
construction, including the band property and the energy identity), the `dSup`-split of
`eq:dvapriori`, the recombination's energy identity, and the three-term rewrite of §9–11.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs5

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs3
open Work.UBBInputs4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The matrix-support form of the band property -/

/-- **The band property in *matrix-support* form**: `A i j = 0` whenever `|i − j| ≥ 3`
(only the supra/infra-diagonals of order `0,1,2` are nonzero).  This is what the `P/Q`-word
computation of FS §7 delivers (through `Work.UBBInputs4.Grading.band_one`/`band_two` at the
corpus's commuting idempotents), and `Work.UBBInputs5.band_of_bandSupport` converts it into
the round-4 `GradedDatum.Band` (`∀ k ≥ 3, dk A nn ψv k = 0`), which is what the
Lieb–Solovej matrix theorem consumes. -/
def BandSupport (A : ℤ → ℤ → ℂ) : Prop :=
  ∀ i j : ℤ, 3 ≤ |i - j| → A i j = 0

/-! ## 2. The sector model: FS's box Hamiltonian over the `n₊`-sectors

FS §7 apply the matrix theorem to the `(n+1)×(n+1)` matrix

    𝒜_{i,j} = ‖1_{n₊=i}Ψ‖⁻¹ ‖1_{n₊=j}Ψ‖⁻¹ ⟨1_{n₊=i}Ψ, H_Λ(μ) 1_{n₊=j}Ψ⟩

and then say: *"Moreover, for the matrix 𝒜, using the notation of
Thm.~\ref{thm:Localizing large matrices}, only the 𝒜^{(k)} with k = 0,1,2 are
non-vanishing."*  The data that produces this statement is a Hilbert space `V`, a
self-adjoint operator `H` (FS's `H_Λ(μ)`), and a self-adjoint resolution of unity `E i` (the
spectral projections `1_{n₊=i}`, `i ∈ iRange n`) with respect to which `H` has band `≤ 2`.
`SectorData` is exactly that list of conditions; `blk`/`sec` are the block matrix and the
vector of sector norms built from it.
-/

/-- **The sector-decomposition data of FS §7**: a self-adjoint `H`, a self-adjoint
resolution of unity by orthogonal idempotents `E i` supported in `iRange n` (so that there
are `n` sectors), and the band condition `E i (H (E j x)) = 0` for `|i − j| ≥ 3`.  The state
`Φ'` is a unit vector. -/
def SectorData (n : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Φ' : V) (H : V →ₗ[ℂ] V) (E : ℤ → V →L[ℂ] V) : Prop :=
  -- `H` is self-adjoint
  (∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) ∧
  -- `E` is a family of orthogonal idempotents
  (∀ i, E i * E i = E i) ∧
  (∀ i j, i ≠ j → E i * E j = 0) ∧
  -- `E` is self-adjoint (the spectral projections of the self-adjoint `n₊`)
  (∀ i x y, inner ℂ (E i x) y = inner ℂ x (E i y)) ∧
  -- `E` is supported in `iRange n`
  (∀ i, i ∉ iRange n → E i = 0) ∧
  -- resolution of unity
  (∑ i ∈ iRange n, E i) = 1 ∧
  -- the band property of `H`: only the sectors `i, i±1, i±2` are coupled
  (∀ i j, 3 ≤ |i - j| → ∀ x, E i (H (E j x)) = 0) ∧
  -- the state is a unit vector
  inner ℂ Φ' Φ' = 1

/-- **The vector of sector norms** `ψv_i = ‖1_{n₊=i}Ψ‖` of FS §7. -/
noncomputable def sec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Φ' : V) (E : ℤ → V →L[ℂ] V) : ℤ → ℂ :=
  fun i => (‖E i Φ'‖ : ℂ)

/-- **The block matrix** `𝒜_{ij} = ⟪1_{n₊=i}Ψ, H 1_{n₊=j}Ψ⟫ / (‖1_{n₊=i}Ψ‖ ‖1_{n₊=j}Ψ‖)`
of FS §7, with the convention *"if any of the norms are zero we set the element to zero"* —
Lean's total division `x / 0 = 0` is exactly that convention, and
`Work.UBBInputs5.blk_mul` records the consequence

    𝒜_{ij} · ‖v_i‖ · ‖v_j‖ = ⟪v_i, H v_j⟫

which holds unconditionally. -/
noncomputable def blk {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Φ' : V) (H : V →ₗ[ℂ] V) (E : ℤ → V →L[ℂ] V) : ℤ → ℤ → ℂ :=
  fun i j => inner ℂ (E i Φ') (H (E j Φ')) / ((‖E i Φ'‖ : ℂ) * (‖E j Φ'‖ : ℂ))

/-- **Round-5 residual for clause (1)** (FS §7 (2)+(3), the *matrix construction*): every
low state of the box `(N,L)` in the dilute regime admits a sector model whose normalised
energy `⟪Φ', HΦ'⟫` reproduces the shifted Rayleigh quotient of `Φ`.

**WARNING (round-5 finding).**  As written this is a *tautology*, provable for every
`3 ≤ M` and `0 ≤ ε₀` (`Work.UBBInputs5.Finding.sectorModelNeu_trivial`): the existential
over `(n, V, Φ', H, E)` is not tied to the box, to `Φ`, or to `H_Λ(μ)` — the witness
`V := ℂ`, `Φ' := 1`, `H := c•id` with `c := RaylNeu N L v Φ − 8π(a v)ρ²L³`, `E 0 := 1` and
`E i := 0` otherwise satisfies `SectorData` and the energy identity.  So clause (1) as a
*residual* carries no analytic content; what it is *meant* to say is FS's `eq:Def_HB` read at
the corpus objects: `V` = (a subspace of) `L²(abox N L)` or the box Fock space `ℱ_s(L²(Λ))`,
`Φ'` the image of `Φ`, `E i = 1_{n₊=i}` and `H = H_Λ(ρ)`.  That identification is the open
obligation (round 4 §4(c)); it is not captured by any residual in this directory.

Kept because `Reduce.Blocks` *proves* the round-4 matrix data (`GradedDatum` with `Band`,
Hermiticity, support, unit `ψv` and the energy identity) from it, so the repaired chain is
logically complete; and because it isolates exactly *where* the missing identification sits.

The statement requires `M ≤ n` and `(⟪Φ',HΦ'⟫).re = RaylNeu N L v Φ − 8π(a v)ρ²L³`. -/
def SectorModelNeu (M : ℕ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) : Prop :=
  3 ≤ M ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∃ (n : ℕ) (V : Type) (i1 : NormedAddCommGroup V) (i2 : InnerProductSpace ℂ V)
        (Φ' : V) (H : V →ₗ[ℂ] V) (E : ℤ → V →L[ℂ] V),
        M ≤ n ∧ @SectorData n V i1 i2 Φ' H E ∧
          (inner ℂ Φ' (H Φ')).re
            = RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-! ## 3. The matrix-form residual of clause (1) -/

/-- **Clause (1) in matrix-support form** (`GradingBlocksNeu` with `Band` replaced by the
*structural* condition `BandSupport gd.A`): a low state admits a Hermitian, supported
`nn × nn` matrix `A` with a unit sector-norm vector `ψv`, the energy identity, and the
*matrix-support* band property `A i j = 0` for `|i − j| ≥ 3`.  `Reduce.Blocks` proves that
this implies the round-4 `GradingBlocksNeu` (the `dk`-bookkeeping `Band` follows from
`BandSupport` by `Grading.BandSupport.dk_eq_zero_of_bandSupport`). -/
def GradingBlocksStructNeu (M : ℕ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) : Prop :=
  3 ≤ M ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∃ (nn : ℕ) (A : ℤ → ℤ → ℂ) (ψv : ℤ → ℂ),
        M ≤ nn ∧
        (∀ i j, A i j ≠ 0 → i ∈ iRange nn ∧ j ∈ iRange nn) ∧
        (∀ i j, A j i = star (A i j)) ∧
        (∀ j, ψv j ≠ 0 → j ∈ iRange nn) ∧
        normSq (iRange nn) ψv = 1 ∧
        BandSupport A ∧
        qform A (iRange nn) ψv ψv
          = RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-! ## 4. The `dSup`-split of `eq:dvapriori` (clause (2)) -/

/-- **Round-5 residual for clause (2) in its *round-4 shape*** (FS §7 (4) =
`eq:dvapriori`), split over the four *directed* off-diagonal expectations: `d_k = dSup k +
dSup (−k)` for `k ≠ 0`, so bounding the four quantities `dSup A n ψ (±1)`, `dSup A n ψ (±2)`
bounds `|d₁| + |d₂|` (`Work.UBBInputs5.Grading.gradingDvNeu_of_dvSup`).

**This clause is FALSE as stated**, for the same reason as `GradingRecombNeu`: it
quantifies over *arbitrary* band `GradedDatum`s, and the only constraint on `A` is the
diagonal identity `energy`.  Take `ψv := (2/√5)e₀ + (1/√5)e₁` (a unit vector for `n ≥ 2`),
`A` Hermitian with `A 0 1 = A 1 0 = 1`, `A 1 1 = 0` and `A 0 0` adjusted so that the energy
identity holds.  Then `A` is band-supported (`A i j = 0` for `|i−j| ≥ 2`) *and* band
(`dk A n ψv k = 0` for `k ≥ 3`, since the supports of `ψv` and `ψv(·+k)` are disjoint), but

    d₁ = dSup A n ψv 1 + dSup A n ψv (−1) = 2/5 + 2/5 = 4/5 ≠ 0 ,

while the right-hand side `K(dens N L)²(a v)(dens N L·(a v)³)^{1/2+η₀}L³` tends to `0` in the
dilute limit `dens N L → 0` (`L → ∞` with `N = 1`, where the constant state is a low state:
`LowStateNeu v 1 L J (const 1) ⟺ 2 ≥ 1 − J√(a³/L⁹)`).  So `GradingDvNeu M K v h J ε₀ η₀` is
false for `M ≥ 2`.

The honest clause is the **model-based** one (`GradingDvModelNeu`): the `dSup` bound for the
block matrix *derived from the Hamiltonian*, which is the object FS's `eq:dvapriori`
estimates. -/
def GradingDvSupNeu (M : ℕ) (K : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Band →
        |dSup gd.A gd.nn gd.ψv 1| + |dSup gd.A gd.nn gd.ψv (-1)|
            + |dSup gd.A gd.nn gd.ψv 2| + |dSup gd.A gd.nn gd.ψv (-2)|
          ≤ K * (dens N L) ^ 2 * (a v) * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3

/-- **The four directed off-diagonal expectations of a *sector-model* block matrix** are at
most `Y`: `|dSup (blk Φ' H E) n (sec Φ' E) (±1)|` and `|·(±2)|`.  This is the bound FS's
`eq:dvapriori` actually produces — for the block matrix *of the Hamiltonian*, not for an
arbitrary matrix. -/
noncomputable def SectorModelDv (n : ℕ) (Y : ℝ) (V : Type) (i1 : NormedAddCommGroup V)
    (i2 : InnerProductSpace ℂ V) (Φ' : V) (H : V →ₗ[ℂ] V) (E : ℤ → V →L[ℂ] V) : Prop :=
  letI := i1
  letI := i2
  |dSup (blk Φ' H E) n (sec Φ' E) 1| + |dSup (blk Φ' H E) n (sec Φ' E) (-1)|
      + |dSup (blk Φ' H E) n (sec Φ' E) 2| + |dSup (blk Φ' H E) n (sec Φ' E) (-2)| ≤ Y

/-- **Round-5 residual for clause (2), model-based** (FS §7 (4) = `eq:dvapriori`, the only
place in the paper where an estimate depends explicitly on `∫v` and not just on `a`): the
four directed expectations of the block matrix *derived from the box Hamiltonian* are at most
`K(dens N L)²(a v)(dens N L·(a v)³)^{1/2+η₀}L³`.

**WARNING (round-5 finding).**  This is *also false as written*
(`Work.UBBInputs5.Finding.gradingDvModelNeu_false`): the quantification is `∀` over model data
with `M ≤ n`, and a model with `E 0, E 1` the coordinate projections and a self-adjoint `H`
coupling the first two sectors gives `blk 0 1 = 1`, hence a `dSup`-sum of `1`, while the
budget at `N = 0`, `L = 1` is `0`.  So clause (2) too cannot be stated without tying the model
to FS's concrete `H_Λ(μ)`; see `README.md` §0.3bis.

By `Work.UBBInputs5.SectorModel.dSup_blk_eq` the four expectations are
`Σ_{i∈iRange n} Re ⟪1_{n₊=i}Ψ, H 1_{n₊=i±k}Ψ⟫`, i.e. the `Q`-word expectations of FS's
display for `d₁`, `d₂` (corpus: `Submission.QCrossD.qcross_d11/d2/d13`,
`Work.QCrossQuarter{,D2}`, `Work.QMassLower`). -/
def GradingDvModelNeu (M : ℕ) (K : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ (n : ℕ) (V : Type) (i1 : NormedAddCommGroup V) (i2 : InnerProductSpace ℂ V)
        (Φ' : V) (H : V →ₗ[ℂ] V) (E : ℤ → V →L[ℂ] V),
        M ≤ n → @SectorData n V i1 i2 Φ' H E →
          (inner ℂ Φ' (H Φ')).re
              = RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3 →
          @SectorModelDv n (K * (dens N L) ^ 2 * (a v)
              * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3) V i1 i2 Φ' H E

/-! ## 5. The recombination (clause (3)) and the round-5 repair

**Round 4's formulation of this clause is false**, and with it the whole round-4 hypothesis
list: `Work.UBBInputs4.GradedDatum.Recomb` quantifies over *every* unit window vector `φ`
and demands `RaylNeu N L v Ψ̃ ≤ qform gd.A (iRange gd.nn) φ φ + 8π(a v)ρ²L³` for some
`Ψ̃`.  The only field of `GradedDatum` constraining `A` is `energy`
(`qform A (iRange nn) ψv ψv = RaylNeu Φ − 8πρ²(a v)L³`), and `qform A φ φ` is *not* bounded
below by it: on *band* data the diagonal entry `A 1 1` is completely free (the `dk` of a
datum with `ψv` concentrated at one index involve only the `ψv`-weighted entries), so the
window vector `φ = e₁` can have `qform A φ φ = −1`, and no `Ψ̃` can satisfy the bound since
`0 ≤ RaylNeu` for `0 ≤ v`.  See `Work.UBBInputs5.gradingRecombNeu_false` and
`Work.UBBInputs5.nPlusGradingNeu_false`: `Work.UBBInputs4.NPlusGradingNeu` is
**unsatisfiable** in the regime of `hpres_of_gradingNeu`, so round 4's end-to-end theorem is
vacuous.

**The root cause** is that `GradedDatum` is an abstraction *of the matrix alone*: it does
not record that `𝒜` is the block matrix of the box Hamiltonian, which is what makes FS's
recombination identity `⟪Ψ̃, HΨ̃⟫ = Σ_{ij}φ̄ᵢ𝒜_{ij}φⱼ` true for every `φ`.  On an arbitrary
`GradedDatum` it is false.  The honest clause is therefore stated at the level where FS
prove it: the Lieb–Solovej localisation theorem (already a theorem of this workspace,
`Work.UBBInputs3.ls_localisation_band2`) selects a *particular* window vector `φ` with

    qform A (iRange nn) φ φ ≤ qform A (iRange nn) ψv ψv + (100/M²)(|d₁| + 4|d₂|)
                              = RaylNeu N L v Φ − 8π(a v)ρ²L³ + (100/M²)(|d₁| + 4|d₂|) ,

and the recombination of *that* `φ` produces a state `Ψ̃` with `⟪Ψ̃, HΨ̃⟫ = ⟪φ,𝒜φ⟫`.  Folding
the two steps together gives the repaired clause `GradingRecombBandNeu`: for every *band*
datum there is `Ψ̃ : CNeu N L` with

    RaylNeu N L v Ψ̃ ≤ RaylNeu N L v Φ + (100/M²)(|d₁| + 4|d₂|)   and   the window.

This clause is what `Chain.lean` consumes, and it is *true* (it is FS's conclusion).  It is
moreover implied by round 4's a-priori window residual `AprioriNPlusNeu`
(`gradingRecombBandNeu_of_apriori`: the original low state `Φ` itself is windowed and
`satisfies` the energy bound) — a *finding* about the round-4 interface, recorded in
`README.md` §4c: at the covariant *expectation* window the `n₊`-localisation step of FS §7
is not needed for §9–11. -/

/-- **Clause (3), the state with the Lieb–Solovej-level energy bound** (FS §7 (5), first
half, with `Work.UBBInputs3.ls_localisation_band2` folded in).  In FS the witness is the
recombination `‖φ̃‖⁻¹Σᵢφ̃ᵢ‖1_{n₊=i}Ψ‖⁻¹1_{n₊=i}Ψ` of the Lieb–Solovej vector `φ`, whose
energy identity `⟪Ψ̃, HΨ̃⟫ = Σ_{ij}φ̄ᵢ𝒜_{ij}φⱼ` is `Work.UBBInputs5.recomb_energy` at the
sector model; the residual here records that a *state of the box class* with that energy
exists.  (Taken alone the clause is weak — `Φ` itself satisfies it — which is exactly why
the window conjunct below carries all the analytic content; the pair is the honest reading
of FS's step (5).) -/
def RecombStateNeu (M : ℕ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Band →
        ∃ Psit : CNeu N L,
          RaylNeu N L v Psit ≤ RaylNeu N L v Φ
            + (100 / (M : ℝ) ^ 2) * (|dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2|)

/-- **Clause (3), the *window*** (FS §7 (5), second half = the a-priori step at the end of
`lem:LocMatrices`): *every* state satisfying the recombined energy bound of
`RecombStateNeu` lies in the covariant `n₊`-window.  This is FS's sentence

> "It remains to prove that `Ψ̃` satisfies (eq:LocalizedNPlus). … This follows from the
> estimate (eq:EnergyBound), `J = ½K_B³`, and (con:KMRKR), which imply that we may use the
> a priori bound (eq:apriorinn+) on the expectation value of `n₊` in `Ψ̃`."

with the error absorbed into the window constant `W`: FS enlarge the localisation length to
`ℳ' + CK_B³K_ℓ⁵ ≤ ℳ` using (con:KBellKM).  Indexing the statement by `Psit` is what makes
the split with `RecombStateNeu` sound: the same `Ψ̃` satisfies both halves. -/
def RecombWindowNeu (M : ℕ) (W : ℕ → ℝ → ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) :
    Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Band →
        ∀ Psit : CNeu N L,
          RaylNeu N L v Psit ≤ RaylNeu N L v Φ
            + (100 / (M : ℝ) ^ 2) * (|dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2|) →
            WindowNeu W N L Psit

/-! ## 5bis. The round-5 **finding** and its repair: the recombination must be band-restricted

Round 4's `Work.UBBInputs4.GradingRecombNeu` quantifies over **every** `GradedDatum`:

    GradingRecombNeu M W v h J ε₀ := ∀ … Φ …, ∀ gd : GradedDatum v N L Φ M, gd.Recomb W

with **no** `gd.Band` hypothesis, whereas the sibling `GradingDvNeu` *does* carry
`gd.Band →` and `GradingBlocksNeu` produces a *band* datum.  `Recomb` asks for
`∃ Ψ̃ : CNeu N L, RaylNeu N L v Ψ̃ ≤ qform gd.A (iRange gd.nn) φ φ + 8π(a v)ρ²L³`, and the
only field of `GradedDatum` constraining `A` is `energy`
(`qform A (iRange nn) ψv ψv = RaylNeu Φ − 8π(a v)ρ²L³`): off-diagonal entries along the
*window* directions are completely free.  Consequently the round-4 clause is **false**:

* take `N = 0`, `L = 1` (so `dens 0 1 = 0`, `RaylNeu 0 1 v Φ = 0`, and *every*
  `Φ : CNeu 0 1` is a low state for every `J`), and the `GradedDatum` with `nn := M`,
  `ψv := 1_{i=0}`, `A := RaylNeu Φ·(e₀e₀*) − e₁e₁*` (Hermitian, supported in `iRange M`,
  energy identity satisfied);
* the window vector `φ := e₁` (unit, supported in `[0,M)`) has `qform A φ φ = −1`, so
  `Recomb` would demand `RaylNeu N L v Ψ̃ ≤ −1 + 8π(a v)·0²·1³ = −1`, while
  `0 ≤ RaylNeu N L v Ψ̃` for `0 ≤ v` (`Work.UBBInputs4.RaylNeu_nonneg`).

Hence `GradingRecombNeu` fails, `NPlusGradingNeu` is **unsatisfiable** in the regime of
`hpres_of_gradingNeu` (any `0 ≤ v`, any `0 < ε₀`, `L = 1`), and round 4's end-to-end
theorem is *vacuous* (see `Work.UBBInputs5.nPlusGradingNeu_false`).  The proof of
`lem:LocMatrices` never uses the non-band data: `locMatricesResidualNeu_of_gradingNeu`
applies `gd.Recomb` only to the datum produced by `GradingBlocksNeu`, which is band.  The
honest clause is therefore the **band-restricted** one below, and the round-5 chain
(`Chain.lean`) is run with `NPlusGradingBandNeu`. -/

/-- **The repaired recombination clause** (the round-5 replacement for
`Work.UBBInputs4.GradingRecombNeu`): for every *band* graded datum of a low state there is
an extended-class state `Ψ̃` with the Lieb–Solovej-level energy bound *and* the covariant
window.  This is FS's step (5) with `Work.UBBInputs3.ls_localisation_band2` folded in, and
it is exactly the conclusion `Chain.lean` needs. -/
def GradingRecombBandNeu (M : ℕ) (W : ℕ → ℝ → ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Band →
        ∃ Psit : CNeu N L,
          RaylNeu N L v Psit ≤ RaylNeu N L v Φ
              + (100 / (M : ℝ) ^ 2) * (|dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2|)
            ∧ WindowNeu W N L Psit

/-- **The repaired `n₊`-grading residual**: the *model* clause (1) (`SectorModelNeu`, which
by `Reduce.Blocks` **proves** the round-4 `GradingBlocksNeu`), the *model-based* clause (2)
`GradingDvModelNeu`, and the repaired clause (3) `GradingRecombBandNeu`.

**WARNING (round-5 finding).**  This list is *unsatisfiable* too
(`Work.UBBInputs5.Finding.nPlusGradingBandNeu_false`): clause (2) is false for every `M ≥ 2`
and `SectorModelNeu` forces `3 ≤ M`.  It is kept only to record that the repaired chain
`Chain.lean` is a valid implication; the usable residual list is round 4's a-priori route
(`Work.UBBInputs5.hpres_of_aprioriWindowNeu`). -/
def NPlusGradingBandNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℕ,
    SectorModelNeu M v h J ε₀ ∧ GradingDvModelNeu M K v h J ε₀ η₀ ∧
      GradingRecombBandNeu M W v h J ε₀

/-! ## 6. The three FS terms of the §9–11 bound -/

/-- The **mean-field (quadratic) term** `4πρ²(a v)L³` of the §9–11 lower bound — the leading
`n₀²` repulsion of FS's second-quantised Hamiltonian. -/
noncomputable def bogQuad (A ρ L : ℝ) : ℝ := 4 * π * ρ ^ 2 * A * L ^ 3

/-- The **LHY gain** `4πρ²(a v)·lhyC·√(ρ(a v)³)·L³` — the Bogoliubov model integral
`lem:BogIntegral`, whose value is the sharp `lhyC = 128/(15√π)`
(`Submission.LhyIntegral.lhy_model_integral_fs`, the corpus's delivered evaluation). -/
noncomputable def bogLhy (A ρ L : ℝ) : ℝ :=
  4 * π * ρ ^ 2 * A * lhyC * Real.sqrt (ρ * A ^ 3) * L ^ 3

/-- The **error term** `4πρ²(a v)·C·(ρ(a v)³)^{1/2+η₀}·L³` of the §9–11 lower bound. -/
noncomputable def bogErr (A C η₀ ρ L : ℝ) : ℝ :=
  4 * π * ρ ^ 2 * A * C * (ρ * A ^ 3) ^ (1 / 2 + η₀) * L ^ 3

end Work.UBBInputs5
