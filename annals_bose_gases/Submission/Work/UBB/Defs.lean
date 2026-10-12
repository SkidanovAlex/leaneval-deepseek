import ChallengeDeps
import Submission.Rhs
import Submission.Work.SboxEB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/UBB` — the UBB assembly (FS `thm:LHY-Box`, the box theorem)

This is the **area** module set for the `UBB` assembly: the per-box canonical
lower bound with the SHARP Lee–Huang–Yang constant `128/(15√π)`, i.e. FS
`final_v2.tex` Theorem `thm:LHY-Box`, in the corpus form consumed by the
CLOSED interface `Submission/UBBtoGc.lean` (see `Submission/STATUS.md`).

## The target

Read `Submission/UBBtoGc.lean` + `Submission/UniformBox.lean` +
`Submission/Work/EndgameCheck.lean`: `UBB` is

```
∃ ε₀ > 0, ∃ C ≥ 0, ∀ L ≥ 1, ∀ N : ℕ,
  (dens N L) * (a v)^3 ≤ ε₀ →
    lhyRhs (a v) C (1/2 + η₀) (dens N L) ≤ boxEnergy N L v / L^3
```

with `dens N L := (N:ℝ)/L³`, `lhyRhs A K s ρ = 4πρ²A(1 + (128/(15√π))√(ρA³) − K(ρA³)^s)`,
`a v` the scattering length.  This module fixes that statement and the whole
dictionary, so that everything downstream (and the lead) can name it.

## What this area delivers

* `Defs.lean` (this file) — the statement `UBB`, the FS-shaped companion
  `FSShape` (the *chemical-potential* form of `thm:LHY-Box`, `μ := dens N L`),
  the per-box dictionary objects `Lambda`/`Theta`/`WordDens`, and the **named
  sibling inputs** (`WordBridge`, `AprioriNPlus`, `BogoliubovLow`,
  `SpectralInput`) in their exact final shapes.
* `Arith.lean` — the parameter arithmetic (all proved): the exact
  `lhyRhs`↔shifted dictionary, the threshold/target comparison that pins the
  choice `J ≥ c = 128/(15√π)`, the infimum dichotomy.
* `Assembly.lean` — the assembly proper: `UBB` from the named inputs, and the
  consumer-facing `hubb` shape of `Submission/UniformBox.lean`.
* `README.md` — the registry of named inputs and the residual/roadmap.

Everything is `sorry`-free and axiom-clean; the *only* content that is not
proved here is carried by the explicitly named hypotheses of the assembly
theorems (`SpectralInput` and its decomposition).

Single import point: `import Submission.Work.UBB.All`.
-/

noncomputable section

open _root_.BoseGases
open Submission.BoseGases
set_option autoImplicit false
set_option linter.dupNamespace false

namespace Work.UBB

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

/-- A scattering solution of `v` (the corpus's `h`-hypothesis). -/
abbrev ScatSol (v : ℝ³ → ℝ) := ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v

/-! ## 1. The dictionary

Names, fixed once and for all (a caller should import these rather than
re-transcribe them). -/

/-- The sharp LHY constant `128/(15√π)` (FS `thm:LHY-Box`; the corpus
`Submission.LhyIntegral.lhy_model_integral_fs` computes it as the value of the
Bogoliubov model integral). -/
noncomputable def lhyC : ℝ := 128 / (15 * √π)

/-- The density of the box `(N, L)`: `N/L³`. -/
def dens (N : ℕ) (L : ℝ) : ℝ := (N : ℝ) / L ^ 3

/-- The LHY right-hand side of the box theorem in the *shifted* (chemical
potential) normalisation used by FS: at density `ρ`, chemical potential `μ = ρ`
and error coefficient `K`,

`Λ A K η₀ ρ = −4πρ²A(1 − c√(ρA³) + K(ρA³)^{1/2+η₀})`,  `c = 128/(15√π)`.

FS's `thm:LHY-Box` reads `e_Λ(μ) ≥ Λ (a v) K η₀ μ` with `μ` the density; the
corpus's `lhyRhs A K (1/2+η₀) ρ = Λ A K η₀ ρ + 8πAρ²` (the
unshifted/canonical form), see `Arith.lhyRhs_eq_shift`. -/
def Lambda (A K η₀ ρ : ℝ) : ℝ :=
  - (4 * π * ρ ^ 2 * A *
      (1 - lhyC * √(ρ * A ^ 3) + K * (ρ * A ^ 3) ^ (1 / 2 + η₀)))

/-- The a-priori threshold of FS `eq:aprioriPsi`, in the shifted normalisation:
at density `ρ` and parameter `J`, a state is *low* when its shifted energy
density is at most `−4πρ²A(1 − J√(ρA³))`. -/
def Theta (A J ρ : ℝ) : ℝ :=
  - (4 * π * ρ ^ 2 * A * (1 - J * √(ρ * A ^ 3)))

/-- The (unshifted) Dirichlet Rayleigh quotient of a box state, in the exact
shape of `boxEnergy`'s body. -/
def Rayl (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) : ℝ :=
  (∫ x in box N L, (Ψ : X N → ℝ) x * 𝓗 N v (Ψ : X N → ℝ) x) /
    (√ (∫ x in box N L, (Ψ : X N → ℝ) x * (Ψ : X N → ℝ) x)) ^ 2

/-- The per-sector **shifted energy density** of a corpus box state: the
`sboxE = kinWord + qLHSword` quotient at chemical potential `μ`, normalised by
the box volume `L³`.  This is the density form of FS's
`⟨Ψ, H_Λ(μ)Ψ⟩/‖Ψ‖²/ℓ³`. -/
def WordDens (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (Φ : X N → ℝ) : ℝ :=
  sboxE N L μ (wPairC L v) (wPairC L (g0 v h)) Φ /
    (L ^ 3 * ∫ x in abox N L, (Φ x) ^ 2)

/-- The infimum of the shifted energy *density* over the corpus box states
`CSBox N L`.  By `Arith`/`Assembly.wordInf_eq_eB_div` this is the corpus
per-box canonical infimum `eB N L μ v h` divided by the box volume `L³`; it is
the object the dichotomy is run on. -/
def wordInf (N : ℕ) (L μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ :=
  ⨅ Φ : CSBox N L, WordDens N L μ v h (Φ : X N → ℝ)

/-! ## 2. The target statements -/

/-- **UBB in the corpus (canonical, unshifted) form**: the uniform dilute box
lower bound at explicit `A`, error coefficient `C` and error exponent `1/2+η₀`.
This is exactly the shape consumed by `Submission.UBBtoGc.hpres_of_UBB` /
`Submission.UniformBox.hbox_of_uniform_box` (their `hubb`). -/
def BoxShape (v : ℝ³ → ℝ) (A C ε₀ η₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * A ^ 3 ≤ ε₀ →
    lhyRhs A C (1 / 2 + η₀) (dens N L) ≤ boxEnergy N L v / L ^ 3

/-- **UBB** at fixed data `v` and error exponent `1/2 + η₀` (the target of this
area, exactly the deliverable): `∃ε₀>0, C≥0` with `A := a v`. -/
def UBB (v : ℝ³ → ℝ) (η₀ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ BoxShape v (a v) C ε₀ η₀

/-- **UBB in the FS (shifted, chemical-potential) normalisation**: the box
density is `ρ := dens N L` and the claim is that the *shifted* box energy
density is at least `Λ`; FS `thm:LHY-Box` verbatim with `μ := ρ`.
`Arith.boxShape_iff_fsShape` proves this is the *same* statement as `BoxShape`
(the shift `8πAρ²` is exact). -/
def FSShape (v : ℝ³ → ℝ) (A C ε₀ η₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * A ^ 3 ≤ ε₀ →
    Lambda A C η₀ (dens N L) ≤ boxEnergy N L v / L ^ 3 - 8 * π * A * (dens N L) ^ 2

/-- `UBB` in the `∃η₀`-packaged shape of `Submission/Work/EndgameCheck.lean`'s
`hubb` (the shape the lead's `theorem_1_2` endgame consumes): there is an error
exponent `η₀` strictly between the target exponent `η` and `1/2`. -/
def UBBExists (v : ℝ³ → ℝ) (η : ℝ) : Prop :=
  ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ η < η₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∃ C : ℝ, 0 ≤ C ∧ BoxShape v (a v) C ε₀ η₀

/-- **The per-state spectral input, Hamiltonian carrier (the primary named
input of this area)** — FS's `eq:ToProve`, stated directly for the canonical
box Rayleigh quotient: for every *low* state of the box `(L,N)` at density
`ρ := dens N L` (shifted energy density at most the a-priori threshold
`Theta (a v) J ρ`), the shifted energy density is at least `Λ`.

This is the whole remaining research content of FS §5–13 in the smallest
possible form: no word, no kernel, no bridge.  The dichotomy in
`Assembly.boxShape_of_spectralH` turns it into `BoxShape` *without any* further
input (in particular without `WordBridge`).  The word-based inputs
(`SpectralInput`, `AprioriNPlus`, `BogoliubovLow`, `WordBridge`) are its
*decomposition* into the sibling chapters' language; see `README.md` §§3–5. -/
def SpectralInputH (v : ℝ³ → ℝ) (J ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Ψ : CInfty0Box N L,
        Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
            ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L)
          ≤ Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2

/-! ## 3. The named sibling inputs -/

/-- **The bridge (named input)** — the corpus per-box canonical infimum
`Submission.Work.SboxEB.eB N L ρ v h` (the infimum of the shifted per-sector
word `sboxE = kinWord + qLHSword` over `CSBox N L`, at chemical potential
`ρ := dens N L`) is *below* the canonical box-energy density minus the exact
chemical-potential shift `8π(a v)ρ²`.

Direction: "the infimum over all particle sectors is ≤ the `N`-sector
canonical energy density minus the shift", i.e. the passage from the canonical
`thm:LHY-Box` to FS's `thm:LHY-Background` (`eq:BackgroundH`: the sector `N` of
`H_μ` is `H_N − 8πaμN`).  It is the only place where the corpus
`kinWord`/`qLHSword` word is compared with the Hamiltonian `𝓗` of
`ChallengeDeps`, so it is a named input here; its proof is corpus
infrastructure (the `A0Core`/`KinPBlockDeps` word identities, the kernel
normalisation `∫w₁ = 8π(a v)` (`Q0Chosen.w1c_acube_integral`), and the trivial
infimum comparison over particle sectors). -/
def WordBridge (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
    wordInf N L (dens N L) v h
      ≤ boxEnergy N L v / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2

/-- The same bridge in the sibling's own language (`eB` instead of `wordInf`);
`Assembly.wordBridge_iff_wordBridgeE` (via `wordInf_eq_eB_div`) shows the two
are the same statement. -/
def WordBridgeE (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
    eB N L (dens N L) v h / L ^ 3
      ≤ boxEnergy N L v / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2

/-- The FS `eq:apriorinn+` shape of an `n₊`-window: `K_B^3 K_ℓ^2 ρ L³ (ρ(a v)³)^{1/2}`
at density `ρ := dens N L`.  `K_ℓ` is a *function* of the box data, as in FS
(their `K_ℓ` is set in `sec:params` in terms of `ℓ` and `μa`); the shape of the
window is not used by the assembly, which only needs the two sibling inputs to
share the *same* window — see `AprioriNPlus`/`BogoliubovLow`. -/
def nPlusWindow (v : ℝ³ → ℝ) (K_B : ℝ) (Kℓ : ℕ → ℝ → ℝ) (N : ℕ) (L : ℝ) : ℝ :=
  K_B ^ 3 * (Kℓ N L) ^ 2 * dens N L * L ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2)

/-- **The a-priori `n₊` window (named input; sibling `SmallBoxSliding`)** — FS
`thm:aprioriHLambda`/`eq:apriorinn+`, second conjunct: a *low* state of the box
of side `L` (shifted energy density at most the a-priori threshold
`Theta (a v) J ρ`) has at most `W N L` excited particles, for a window function
`W` that the two sibling inputs of this area SHARE (the FS shape of `W` is
`nPlusWindow`; the assembly only needs that `BogoliubovLow` consumes the same
function, and the constants of `W` are free for `theorem_1_2`).

The corpus chain delivering this is
`Work.SmallBoxSliding.Assembly.apriori_nplus_window_assembly` (CLOSED) fed by
`Work.SmallBoxSliding.Sliding.sliding_sum_identity*` (the localisation
`hslide`, FS `eq:BSsliding2`, cited from Bratteli–Solovej Thm 3.10),
`Work.SmallBoxTBWord.Sliding.tBLocalisation` (the `𝒯_B` kinetic residual),
`Work.SmallBoxDLBound.smallbox_dl_energy_bound` (FS `thm:smallbox`) and the
`Work.SmallBoxA0` block bound; the *energy* input `eq:aprioriPsi` is `hEgc`,
owned by `Work.SecondOrder`/`Work.TrialState`.  `Work.UBB.Apriori` shows that
this input's *arithmetic* is CLOSED given the per-state sliding inequality.

Stated at the box level with the density fixed at `ρ := dens N L` (so that the
*particle*-window conjunct of `eq:apriorinn+` is vacuous — the canonical box
statement has no free particle number). -/
def AprioriNPlus (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ : ℝ) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CSBox N L,
      WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
      cnPlus L (Φ : X N → ℝ) ≤ W N L

/-- **The Bogoliubov lower bound under the `n₊` window (named input; sibling
`SmallBoxBogolubov*`, FS §9–11)** — the second-quantisation + `c`-number
substitution + Bogoliubov diagonalisation step (FS `prop:Hamilton2ndQuant`,
`thm:Kafz`, `thm:BogHamDiag`, `lem:BogIntegral`, `thm:Control3Q`): once the
excited count of a *low* state is below the shared window `W`, its shifted
energy density is at least `Λ` for some coefficient `C` (the `X^{1/5}`/`K_ℓ^{-1}`
errors of FS's `eq:ToProve` are absorbed into `C`, which is O(1) for
`theorem_1_2` — see `SmallBoxDesignNote.md` "Session-100b"; only the SHARP
`c = 128/(15√π)` and the exponent `1/2+η₀` are rigid, and they are explicit
here).  The sharp constant's provenance (the model integral) is recorded in
`Work.UBB.LhyConstant`. -/
def BogoliubovLow (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        cnPlus L (Φ : X N → ℝ) ≤ W N L →
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L) ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)

/-- **The per-state spectral input (the single deep named input of this area)**
— FS `eq:ToProve` in its cleanest form: for every low state of the box `(L, N)`
at density `ρ := dens N L` (shifted energy density at most the a-priori
threshold `Theta (a v) J ρ`), the shifted energy density is at least `Λ`.

The whole remaining research content of FS §5–13 sits in this statement; it is
decomposed in `Assembly.lean` into the two sibling inputs `AprioriNPlus`
(FS `thm:aprioriHLambda`) and `BogoliubovLow` (FS §9–11), and the *arithmetic*
of that decomposition is proved. -/
def SpectralInput (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CSBox N L,
        WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
        Lambda (a v) C η₀ (dens N L) ≤ WordDens N L (dens N L) v h (Φ : X N → ℝ)

end Work.UBB
