import ChallengeDeps
import Submission.Work.ESYUpper.ModeStage
import Submission.Work.SmallBoxL2Modes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ESYStage` — the ESY stage grind (round 4 of the upper-bound chapter)

This chapter takes up the named residual `Work.ESYUpper.ModeStage`
(module `Submission/Work/ESYUpper/ModeStage.lean`) — the two remaining stages of
the ESY / Yau–Yin upper-bound computation — and *fixes the vocabulary* of the
stage so that the two conjuncts become two precisely stated, independently
attackable residuals **about concrete objects of the box**:

* **the box mode lattice** `modeSet ℓ n` — the wave-vectors `π k / ℓ`,
  `k ∈ {0,…,n}³ \ {0}`, of the corpus's Neumann/cosine box modes
  (`Submission.Work.SmallBoxFourierBasis`, `Submission.Work.SmallBoxL2Modes`);
* **the orthonormal mode family** `neuMode ℓ k` (the normalised product Neumann
  mode) and the **diagonal pairing kernel** `diagKernel ℓ n c` — the ESY ansatz
  `G x y = Σ_k c_k φ_k(x)φ_k(y)`, whose diagonality at the family is *proved*
  (`Submission/Work/ESYStage/Neumann.lean`);
* **the concrete ESY state** `esyState N ℓ μ v h n` — the pair-excited state
  with the uniform condensate `ψ ≡ 1`, the exponential squeezing weights
  `wt m = 1/(2^m m!)` (`bogWeight 1`) and the mode amplitudes
  `c_k = e_k/(1−e_k)` at the ESY optimal amplitude `e_k = optAmp` — exactly
  ESY's ansatz `exp(½ Σ_p c_p a†_p a†_{−p})` in the box's mode basis;
* **the ESY mode data**: the lattice Fourier coefficients `modeV`, `modeG`,
  `modeF` of the corpus's cutoff potentials `wScaled ℓ v`, `wScaled ℓ (g0 v h)`;
* **the ESY mode functional** `esyModeFun` — the right-hand side of ESY's
  Lemma `lm:EM`/`lm:E`, i.e. `−4πaμN + esyQ + Ω₂ + Ω₄` at the optimal
  amplitudes.

The two stages are then

* `ESYStageEnergy` (**stage E**, ESY Lemma `lm:EM`): the energy word of the
  concrete state is at most the ESY mode functional — the position-space ↔
  momentum-space dictionary plus the Wick evaluation;
* `ESYStageIneq` (**stages Ω + L + N2**): the mode functional satisfies the
  momentum-space Rayleigh inequality against the norm square `pairStateZ`.

`ESYStageNorm` (the positivity of the norm square — the Wick/normalisation
identity) is the third residual; the *structural* facts (symmetry of the kernel,
continuity of the state, diagonality in the mode family) are **proved** here, so
that they are not part of any residual.

The main results of the chapter are the reductions
(`Submission/Work/ESYStage/Reductions.lean`)

    ESYStage        ⟹  ModeStageLE  ⟹  PairFamilyBound
    ESYStage        ⟹  SecondOrder.SecondOrderUpperBound'
    ESYStage        ⟹  the consumer's `hEgc`  (any `J ≥ C`)

and `Work.ESYUpper.ModeStage ⟹ ModeStageLE` (nothing of round 3 is lost).

## Why the round-3 residual is restated

`ModeStage` asks for an *equality* `pairStateE = (ESY mode functional)` and
leaves the mode data `(s, Λ, Vup, p2, V, f, Vsub, V2p)` — hence also the value
of the mode functional — existentially free.  Both features are unnecessary for
the reduction (which only ever uses the inequality chain
`pairStateE ≤ M ≤ θ_C·Z`) and the freedom makes the statement *weaker* than the
ESY computation while the equality makes it *unprovable* where ESY only proves
`E ≤ 4πaNϱ + Q + O(…)`.  `ModeStageLE` is the residual with the equality
replaced by `≤` (round 3 is recovered by `ModeStage → ModeStageLE`), and
`ESYStage` is the same residual for the *concrete* box data.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.ESYStage

open Submission.BoseGases
open _root_.BoseGases
open Work.SecondOrder
open Work.ESYUpper

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The box mode lattice and the mode family -/

/-- The **finite index set of the box's excited modes**: the triples
`(k₀,k₁,k₂)` with `0 ≤ kᵢ ≤ n`, with the all-zero triple (`k = 0`, the
condensate direction) removed.  A finite type, hence usable as the index of the
orthonormal family of `Work.ESYUpper.DiagonalKernel`. -/
abbrev ModeIdx (n : ℕ) :=
  {k : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
    k ≠ ((0 : Fin (n + 1)), ((0 : Fin (n + 1)), (0 : Fin (n + 1))))}

instance (n : ℕ) : Fintype (ModeIdx n) := by
  dsimp [ModeIdx]
  infer_instance

instance (n : ℕ) : DecidableEq (ModeIdx n) := by
  dsimp [ModeIdx]
  infer_instance

/-- The multi-index `Fin 3 → ℕ` attached to a box mode index. -/
def modeVec {n : ℕ} (k : ModeIdx n) : Fin 3 → ℕ :=
  ![(k.val.1 : ℕ), (k.val.2.1 : ℕ), (k.val.2.2 : ℕ)]

/-- The **wave-vector** of a Neumann mode: `p_j = π k_j / ℓ`.  This is the
momentum conjugate to the cosine mode `cos((k_j π/ℓ)(x_j + ℓ/2))`. -/
noncomputable def neuWave (ℓ : ℝ) (k : Fin 3 → ℕ) : ℝ³ :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun j => Real.pi * (k j : ℝ) / ℓ)

/-- The **box mode set**: the wave-vectors of the excited box modes — the finite
truncation `{π k / ℓ : k ∈ {0,…,n}³, k ≠ 0}` of the orthant lattice.  This is
ESY's mode set `Λ* \ {0}` (in the cosine/Neumann normalisation of the centred
box). -/
noncomputable def modeSet (ℓ : ℝ) (n : ℕ) : Finset ℝ³ :=
  Finset.univ.image (fun k : ModeIdx n => neuWave ℓ (modeVec k))

/-- The **lattice gap** of the mode set: `π/ℓ` — the minimal distance between
two distinct modes, and the minimal norm of a mode
(`Submission/Work/ESYStage/Lattice.lean`). -/
noncomputable def modeGap (ℓ : ℝ) : ℝ := Real.pi / ℓ

/-- The **normalised product box-Neumann mode** `φ_k`: the product of the 1-D
Neumann modes `cos((k_j π/ℓ)(x_j + ℓ/2))` divided by the square root of its
box norm.  `Submission/Work/ESYStage/Neumann.lean` proves that
`∫_{acube ℓ} φ_k φ_l = δ_{kl}` — the orthonormal family of
`Work.ESYUpper.DiagonalKernel`. -/
noncomputable def neuMode (ℓ : ℝ) (k : Fin 3 → ℕ) : ℝ³ → ℝ :=
  fun x => (Real.sqrt (∏ j : Fin 3, coordSqNorm ℓ (k j)))⁻¹ * boxNeumann3 ℓ k x

/-- The **diagonal pairing kernel** of the ESY ansatz: the finite-rank symmetric
kernel `G x y = Σ_k c_k φ_k(x) φ_k(y)` in the box's orthonormal mode family.
This is the position-space form of `exp(½ Σ_p c_p a†_p a†_{−p})|0⟩` restricted to
the box mode basis. -/
noncomputable def diagKernel (ℓ : ℝ) (n : ℕ) (c : ModeIdx n → ℝ) : ℝ³ → ℝ³ → ℝ :=
  fun x y => ∑ k : ModeIdx n, c k * neuMode ℓ (modeVec k) x * neuMode ℓ (modeVec k) y

/-! ## The lattice Fourier data (ESY's `V̂_p`, `ĝ_p`, `f̂_p`) -/

/-- The **lattice Fourier coefficient** (cosine transform over the centred box)
of a radial kernel `F`:
`F̂_p = ∫_{acube ℓ} F(z)·cos(⟨p,z⟩) dz`.
For `p` a box mode wave-vector this is ESY's `F̂_p` (their `V̂_p`, `ĝ_p`, …). -/
noncomputable def latFourier (ℓ : ℝ) (F : ℝ³ → ℝ) (p : ℝ³) : ℝ :=
  ∫ z in acube ℓ, F z * Real.cos (inner ℝ p z)

/-- `V̂_p` — the lattice Fourier coefficient of the cutoff two-body potential. -/
noncomputable def modeV (ℓ : ℝ) (v : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun p => latFourier ℓ (wScaled ℓ v) p

/-- `ĝ_p` — the lattice Fourier coefficient of `g₀ = v(1−w₀)`, the corpus's
`g0 v h` (ESY's `ĝ = V̂ − f̂`). -/
noncomputable def modeG (ℓ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : ℝ³ → ℝ :=
  fun p => latFourier ℓ (wScaled ℓ (g0 v h)) p

/-- `f̂_p = V̂_p − ĝ_p` — the lattice Fourier coefficient of `f = v·w₀`
(ESY's scattering-equation coefficient; defined here as ESY's `f = V − g`). -/
noncomputable def modeF (ℓ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : ℝ³ → ℝ :=
  fun p => modeV ℓ v p - modeG ℓ v h p

/-- The **kinetic energy of a mode**, `p² = ‖p‖²` (ESY's `p²`). -/
def modeP2 (p : ℝ³) : ℝ := ‖p‖ ^ 2

/-- The **ESY optimal amplitude** `e_p = argMin (‖p‖²/ϱ) V̂_p f̂_p` of a mode
(`Work.ESYUpper.argMin`, ESY's eq. `(ep)`), at `ϱ = μ` and the lattice Fourier
data of the box. -/
noncomputable def esyAmp (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (p : ℝ³) : ℝ :=
  optAmp μ (modeV ℓ v) (modeF ℓ v h) p

/-- ESY's **squeezing amplitude** `c_p = e_p/(1−e_p)` (their relation `(rel)`),
the coefficient of the diagonal kernel. -/
noncomputable def squeezeAmp (e : ℝ) : ℝ := e / (1 - e)

/-- The **concrete ESY kernel**: the diagonal kernel in the box mode family at
the ESY squeezing amplitudes `c_k = e_k/(1−e_k)`, `e_k = esyAmp` at the mode's
wave-vector. -/
noncomputable def esyKernel (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) : ℝ³ → ℝ³ → ℝ :=
  diagKernel ℓ n (fun k => squeezeAmp (esyAmp ℓ μ v h (neuWave ℓ (modeVec k))))

/-! ## The ESY trial state and the mode functional -/

/-- The **concrete ESY trial state** of the chapter: the pair-excited state with
uniform condensate `ψ ≡ 1`, exponential squeezing weights `wt m = 1/(2^m m!)`
(so that the pair kernel carries the whole amplitude), and the ESY diagonal
kernel.  Its `N`-particle component is the fixed-`N` projection of
`exp(½ Σ_p c_p a†_p a†_{−p})|0⟩` in the box's mode basis. -/
noncomputable def esyState (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) : X N → ℝ :=
  pairState N (fun _ => 1) (bogWeight 1) (esyKernel ℓ μ v h n)

/-- The **ESY mode functional**: the right-hand side of ESY's Lemma `lm:EM`
combined with `lm:E`, i.e.

`−4πaμN + Q + Ω₂ + Ω₄`,

at the optimal amplitudes and the box's lattice Fourier data.  This is the
quantity ESY minimise/estimate to obtain `Q(0) + O(Nϱ²|log ϱ|)`. -/
noncomputable def esyModeFun (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (s : Finset ℝ³) : ℝ :=
  - 4 * π * (a v) * μ * (N : ℝ)
    + esyQ s μ modeP2 (modeV ℓ v) (modeF ℓ v h)
    + Omega2 s (modeV ℓ v 0) (ℓ ^ 3) (modeV ℓ v) (optAmp μ (modeV ℓ v) (modeF ℓ v h))
    + Omega4 s (modeV ℓ v 0) (ℓ ^ 3) (fun p r => modeV ℓ v (p - r)) (fun p => modeV ℓ v (2 • p))
        (optAmp μ (modeV ℓ v) (modeF ℓ v h))

/-- The **ESY energy threshold** of the residual: `θ_C = −4πμ²(a v)ℓ³(1−C(μ(a v)³)^{1/2})`. -/
noncomputable def thetaC (μ C ℓ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 - C * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))

/-! ## The three stage residuals -/

/-- **Stage N — the norm square (Wick evaluation of the double sum).**  The
concrete ESY state has nonzero (indeed positive) box norm square: the value
`Σ_{p,q} w_p w_q ∫ pairComp_p pairComp_q > 0` of the ESY normalisation. -/
def ESYStageNorm (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) : Prop :=
  0 < pairStateZ N ℓ (fun _ => 1) (bogWeight 1) (esyKernel ℓ μ v h n)

/-- **Stage E — the energy evaluation (ESY Lemma `lm:EM`), in Rayleigh-quotient
form.**  The *Rayleigh quotient* of the concrete ESY state is at most the ESY
mode functional:

`pairStateE ≤ esyModeFun · pairStateZ`.

The quotient form is the correct one, and it is exactly ESY's own structure:
their `lm:EM` evaluates the *normalised* energy `E = ⟨H⟩_Ψ` of the state in
terms of the amplitudes, i.e. the quotient of the numerator `pairStateE` by the
norm square `pairStateZ`; the two objects live on different scales (both are
`∫`-integrals over the `3N`-dimensional box, while `esyModeFun` is an
`N`-particle energy), so only their quotient is comparable with `esyModeFun`.
The Rayleigh reduction (`pairFamilyBound_of_rayleigh`) then only ever uses the
quotient, so nothing is lost — and the norm square is *never* evaluated: only
its positivity `ESYStageNorm` enters. -/
def ESYStageEnergy (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) : Prop :=
  pairStateE N ℓ μ v h (fun _ => 1) (bogWeight 1) (esyKernel ℓ μ v h n)
    ≤ esyModeFun N ℓ μ v h (modeSet ℓ n)
        * pairStateZ N ℓ (fun _ => 1) (bogWeight 1) (esyKernel ℓ μ v h n)

/-- **Stages Ω + L — the momentum-space inequality.**  The ESY mode functional
obeys the threshold inequality `esyModeFun ≤ thetaC μ C ℓ v`: the `Ω₂ + Ω₄`
remainder control (stage Ω, closed on the box data modulo `ModeDataBounds` by
`esyStageOmega_of_amplitudeBounds`), the mode-sum bound on `esyQ` (stage L,
whose *value* `4πaNϱ·(128/(15√π))(a³ϱ)^{1/2}` is proved in
`EsyQ_const`/`EsyQLimitValue`), the minimisation over the amplitudes (ESY's
`le-ep`, proved per mode) and the final scalar arithmetic (`ESYStageArith`).

*No norm square occurs*: the momentum inequality is a statement about the
functional only.  The norm enters the reduction only through its **positivity**
(`ESYStageNorm`), as in ESY's own normalisation of the trial state. -/
def ESYStageIneq (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) : Prop :=
  esyModeFun N ℓ μ v h (modeSet ℓ n) ≤ thetaC μ C ℓ v

/-- **The ESY stage residual** for the concrete box data: some truncation `n`
gives a state (the concrete one) whose norm square is positive (stage N), whose
**Rayleigh quotient** is dominated by the ESY mode functional (stage E), and
whose mode functional satisfies the threshold inequality (stages Ω + L).

Together with the positivity of the norm (`pairStateZ_nonneg`, proved) and the
Rayleigh reduction (`pairFamilyBound_of_rayleigh`, proved) this gives the
pair-family residual, hence `SecondOrderUpperBound'` and the consumer's
`hEgc`: cf. `Reductions.lean`. -/
def ESYStageResidual (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ n : ℕ, ESYStageNorm N ℓ μ v h n ∧ ESYStageEnergy N ℓ μ v h n
    ∧ ESYStageIneq N ℓ μ C v h n

/-- The **dilute-window** form of the ESY stage residual. -/
def ESYStageBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → ESYStageResidual N ℓ μ C v h

/-! ## The round-3 residual in the form the reduction actually uses -/

/-- **`ModeStage` with the energy identity relaxed to an inequality.**  This is
`Work.ESYUpper.ModeStage` with the first conjunct weakened from
`pairStateE = (mode functional)` to `pairStateE ≤ (mode functional)` — the only
form of it the reduction to `PairFamilyBound` ever uses.  Round 3 is recovered:
`ModeStage → ModeStageLE` (`Submission/Work/ESYStage/Reductions.lean`). -/
def ModeStageLE (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  ∃ (ψ : ℝ³ → ℝ) (wt : ℕ → ℝ) (G : ℝ³ → ℝ³ → ℝ) (s : Finset ℝ³) (Λ Vup : ℝ)
    (p2 V f : ℝ³ → ℝ) (Vsub : ℝ³ → ℝ³ → ℝ) (V2p : ℝ³ → ℝ),
    (∀ x y : ℝ³, G x y = G y x) ∧ Continuous (pairState N ψ wt G) ∧
      DiagonalKernel ℓ G ∧ 0 < pairStateZ N ℓ ψ wt G ∧ 0 < Λ ∧ Λ = ℓ ^ 3 ∧
      (∀ p ∈ s, p2 p = ‖p‖ ^ 2) ∧
      pairStateE N ℓ μ v h ψ wt G
        ≤ - 4 * π * (a v) * μ * (N : ℝ)
          + esyQ s μ p2 V f + Omega2 s Vup Λ V (optAmp μ V f)
          + Omega4 s Vup Λ Vsub V2p (optAmp μ V f) ∧
      (- 4 * π * (a v) * μ * (N : ℝ)
          + esyQ s μ p2 V f + Omega2 s Vup Λ V (optAmp μ V f)
          + Omega4 s Vup Λ Vsub V2p (optAmp μ V f)
        ≤ thetaC μ C ℓ v * pairStateZ N ℓ ψ wt G)


/-! ## The ESY data bounds (`(cond2)`-type inputs) -/

/-- The **ESY data bounds** on the box mode data: the lattice-Fourier form of
ESY's Lemma `lemma:scatt` (their `(cond2)` and `(lip)`) together with the
positivity and monotonicity of the Fourier coefficients of a nonnegative kernel
that the `Ω₂`/`Ω₄` estimates consume.

These are *inputs* of the chapter, not residuals: `(cond2)` (`0 < f̂₀, ĝ₀ < V̂₀`)
and the Lipschitz bounds `(lip)` are ESY's Lemma `lemma:scatt` for the
scattering data, and the sign/monotonicity facts (`0 ≤ V̂_p ≤ V̂_0`, `V̂_{2p} ≤ V̂_0`)
follow from the positivity of the potential in the small-coupling regime. -/
def ModeDataBounds (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) (f0 V0 g0 : ℝ) : Prop :=
  0 < f0 ∧ 0 < V0 ∧ 0 ≤ g0 ∧
    (∀ p ∈ modeSet ℓ n, f0 ≤ modeF ℓ v h p) ∧
    (∀ p ∈ modeSet ℓ n, V0 ≤ modeV ℓ v p) ∧
    (∀ p ∈ modeSet ℓ n, |modeV ℓ v p - modeF ℓ v h p| ≤ g0) ∧
    0 ≤ modeV ℓ v 0 ∧
    (∀ p ∈ modeSet ℓ n, modeV ℓ v p ≤ modeV ℓ v 0) ∧
    (∀ p ∈ modeSet ℓ n, 0 ≤ modeV ℓ v p) ∧
    (∀ p ∈ modeSet ℓ n, ∀ r ∈ modeSet ℓ n, modeV ℓ v (p - r) ≤ modeV ℓ v 0) ∧
    (∀ p ∈ modeSet ℓ n, 0 ≤ modeV ℓ v (2 • p)) ∧
    (∀ p ∈ modeSet ℓ n, modeV ℓ v (2 • p) ≤ modeV ℓ v 0)

/-- The **dilute-window form of `ModeStageLE`** (the round-3 residual in the
inequality form), i.e. `1 ≤ N → μ(a v)³ ≤ ε → ModeStageLE …`. -/
def ModeStageLEBound' (N : ℕ) (ℓ μ C ε : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop :=
  1 ≤ N → μ * (a v) ^ 3 ≤ ε → ModeStageLE N ℓ μ C v h


/-! ## The four named sub-stages of the second conjunct -/

/-- **Stage L** (ESY's eqs. `(integr)`, `(8)`, `(8-1)`): the mode-sum bound on
the ESY second-order term `esyQ` over the box mode set.  The *value* of the
limit (`4πaNϱ·(128/(15√π))(a³ϱ)^{1/2}`) is proved in the delivered
`EsyQ_const`/`EsyQLimitValue`/`PhiESY_zero`. -/
def ESYStageQ (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) (Qval : ℝ) : Prop :=
  esyQ (modeSet ℓ n) μ modeP2 (modeV ℓ v) (modeF ℓ v h) ≤ Qval

/-- **Stage Ω** (ESY's `(neg0)`–`(neg6)`): the two-body/four-body remainder
bound on the box mode data, with `Ω₂`/`Ω₄` in their `θ`-form at the optimal
amplitudes.  This sub-stage is *closed* modulo the data bounds
`ModeDataBounds`: `boxOmegaStage` (with the amplitude sum bounds supplied by
`boxAmplitudeBounds`) proves it. -/
def ESYStageOmega (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) (Err : ℝ) : Prop :=
  Omega2 (modeSet ℓ n) (modeV ℓ v 0) (ℓ ^ 3) (modeV ℓ v)
      (optAmp μ (modeV ℓ v) (modeF ℓ v h))
    + Omega4 (modeSet ℓ n) (modeV ℓ v 0) (ℓ ^ 3) (fun p r => modeV ℓ v (p - r))
        (fun p => modeV ℓ v (2 • p)) (optAmp μ (modeV ℓ v) (modeF ℓ v h))
    ≤ Err

/-- **Stage N2** (the Wick/normalisation evaluation): an upper bound on the norm
square of the concrete ESY state — the ESY Fock norm `∏_p (1−|c_p|²)^{−1/2}`,
transported to the fixed-`N` component.  This is the sub-stage that the
`N = 2` computation `pairStateZ_two_eq` opens.

*Not on the critical path*: the Rayleigh form of the residual needs only the
**positivity** of `pairStateZ` (`ESYStageNorm`), not its value — the value is
needed only if one wants the *explicit* normalisation of the state (e.g. for the
Fock-space comparison of ESY's paper).  The exact evaluation, however, is the
template for stage N (`pairStateZ_two_eq`, `pairOverlap_self_diagKernel`,
`pairOverlap_four_cycle`). -/
def ESYStageNormEval (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (n : ℕ) (Z₀ : ℝ) : Prop :=
  pairStateZ N ℓ (fun _ => 1) (bogWeight 1) (esyKernel ℓ μ v h n) ≤ Z₀

/-- **The final arithmetic** of the momentum-space inequality: the scalar
comparison of the mode functional with the threshold, at the (upper) norm bound
`Z₀`.  This is where the constant `C` and the dilute window
`μ(a v)³ ≤ ε` enter. -/
def ESYStageArith (N : ℕ) (ℓ μ C : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (Qval Err : ℝ) : Prop :=
  - 4 * π * (a v) * μ * (N : ℝ) + Qval + Err ≤ thetaC μ C ℓ v

end Work.ESYStage


