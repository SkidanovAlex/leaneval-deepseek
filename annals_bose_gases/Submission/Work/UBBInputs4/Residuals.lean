import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.UBBInputs4.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.UBBInputs4.Residuals` — the residuals of FS §7 and §9–11 at the extended class

This is round 4's answer to the **state-class finding** of
`Submission/Work/UBBInputs3/README.md` §2.  Round 3 stated FS §7's `lem:LocMatrices` and FS
§9–11 as residuals at the *Dirichlet* class `CInfty0Box`; but FS's localised state

    Ψ̃ = ‖φ̃‖⁻¹ Σᵢ φ̃ᵢ ‖1_{n₊=i}Ψ‖⁻¹ 1_{n₊=i}Ψ

is *not* in that class (the `1_{n₊=i}` are polynomials in the mean projections `Pᵢ`, and
`PᵢΨ` is constant in the `i`-th coordinate, so it does not vanish outside the box).  FS's
own states live in `ℱ_s(L²(Λ))` with `Λ` the box *and their box Hamiltonian is the Neumann
one* — so the faithful formalisation of §7 and §9–11 is at the **extended (Neumann) class
`CNeu`** of `Work.UBBInputs4.ExtClass`.  Everything in this file is therefore stated at
`CNeu`, with the **covariant windows** `WindowNeu W N L Φ := cnPlus L Φ ≤ W N L · aboxSq N L Φ`
(`aboxSq` = the mass on the centred box `abox N L`, the cube on which `Qᵢ` is defined; see
`cnPlus_eq_qform_nPlus`, which identifies `cnPlus` with the quadratic form of `n₊ = ΣᵢQᵢ`).

## The two residuals (the shortest hypothesis list of Route H)

* **`LocMatricesResidualNeu`** — FS §7 `lem:LocMatrices` at the extended class: a low state
  is replaced by a windowed state at the energy cost `4πρ²(a v)K(ρ(a v)³)^{1/2+η₀}L³`.
* **`BogoliubovWindowedNeu`** — FS §9–11 with the window hypothesis only, at the extended
  class.

`locMatricesResidualNeu_of_gradingNeu` reduces the first to the **`n₊`-grading**
`NPlusGradingNeu`, which is stated as the conjunction of *three separately attackable*
clauses (this is the round-4 refinement of round 3's monolithic `NPlusGrading`):

| clause | FS reference | content |
|---|---|---|
| `GradingBlocksNeu` | §7 (2)+(3) | the block matrix `𝒜` of the `n₊`-decomposition exists and has band ≤ 2, with the energy identity `⟨ψ,𝒜ψ⟩ = ⟨Ψ,H_ΛΨ⟩` |
| `GradingDvNeu` | §7 (4) = `eq:dvapriori` | the `d₁, d₂` bound, **the only place `∫v` appears** in FS |
| `GradingRecombNeu` | §7 (5) | the recombination `Ψ̃ = Σᵢ φᵢ‖1_{n₊=i}Ψ‖⁻¹1_{n₊=i}Ψ` back into a state, with the `n₊`-window |

The grading datum is the structure `GradedDatum` (the matrix `𝒜`, the unit vector
`ψᵢ = ‖1_{n₊=i}Ψ‖`, the energy identity), and the three clauses are predicates on it
(`GradedDatum.Band`, `.Dv`, `.Recomb`).  This is the precise form of the roadmap's
"the spectral/grading infrastructure: the operator `n₊ = ΣᵢQᵢ`, its integer spectrum and
its spectral projections": the *algebra* of those projections is
`Work.UBBInputs4.Grading.lagrange_spec` (with `Work.UBBInputs4.Grading.idem_annihilator`),
so `GradingBlocksNeu` is now *pinned to a definite construction* rather than to an
unspecified matrix; the remaining analytic content of `GradingBlocksNeu` is the band
property (the potential changes `n₊` by at most 2) and the energy identity.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs
open Work.UBBInputs2
open Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The two Route-H residuals at the extended class -/

/-- **FS §7 `lem:LocMatrices` at the extended class** (the residual of Route H, first
hypothesis).  A low extended state is replaced by a windowed extended state at energy cost
`4πρ²(a v)K(ρ(a v)³)^{1/2+η₀}L³` — FS's `eq:EnergyBound` with the error at the exponent of
the target `Λ` (the absorption of `eq:LargeMatricesNew`). -/
def LocMatricesResidualNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
        ∃ Psit : CNeu N L,
          RaylNeu N L v Psit
              ≤ RaylNeu N L v Φ
                + 4 * π * (dens N L) ^ 2 * (a v) * K
                    * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3
          ∧ WindowNeu W N L Psit

/-- **FS §9–11 with the window hypothesis only, at the extended class** (the residual of
Route H, second hypothesis): a windowed extended state has shifted energy density at least
`Λ(a v) C η₀ ρ`. -/
def BogoliubovWindowedNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
      ∀ Φ : CNeu N L, WindowNeu W N L Φ →
        Lambda (a v) C η₀ (dens N L) * L ^ 3
          ≤ RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

/-! ## 2. The absorption of `lem:LocMatrices` into the `Λ`-coefficient -/

/-- **The arithmetic of FS `eq:LargeMatricesNew`**, isolated: if the localised state's
shifted energy is at most that of the original state, then the absorption `C ↦ C + K` of the
`Λ`-coefficient is *exact* (the coefficient is linear with the negative slope
`−4πρ²A(ρA³)^{1/2+η₀}`). -/
theorem lambda_shift_le {A C K η₀ ρ U V L : ℝ} (hL : 0 < L)
    (h1 : Lambda A C η₀ ρ * L ^ 3 ≤ U - 8 * π * A * ρ ^ 2 * L ^ 3)
    (h2 : U ≤ V + 4 * π * ρ ^ 2 * A * K * (ρ * A ^ 3) ^ (1 / 2 + η₀) * L ^ 3) :
    Lambda A (C + K) η₀ ρ ≤ V / L ^ 3 - 8 * π * A * ρ ^ 2 := by
  have h3 : (0 : ℝ) < L ^ 3 := by positivity
  have hid : Lambda A (C + K) η₀ ρ
      = Lambda A C η₀ ρ - 4 * π * ρ ^ 2 * A * K * (ρ * A ^ 3) ^ (1 / 2 + η₀) := by
    unfold Lambda
    ring
  have hdiv : (U - 8 * π * A * ρ ^ 2 * L ^ 3) / L ^ 3
      = U / L ^ 3 - 8 * π * A * ρ ^ 2 := by
    field_simp
  have hdiv2 : (V + 4 * π * ρ ^ 2 * A * K * (ρ * A ^ 3) ^ (1 / 2 + η₀) * L ^ 3) / L ^ 3
      = V / L ^ 3 + 4 * π * ρ ^ 2 * A * K * (ρ * A ^ 3) ^ (1 / 2 + η₀) := by
    field_simp
  have h1' : Lambda A C η₀ ρ ≤ U / L ^ 3 - 8 * π * A * ρ ^ 2 := by
    have h := div_le_div_of_nonneg_right h1 h3.le
    rw [hdiv] at h
    rwa [mul_div_cancel_right₀ _ (ne_of_gt h3)] at h
  have h2' : U / L ^ 3 ≤ V / L ^ 3 + 4 * π * ρ ^ 2 * A * K * (ρ * A ^ 3) ^ (1 / 2 + η₀) := by
    have h := div_le_div_of_nonneg_right h2 h3.le
    rwa [hdiv2] at h
  rw [hid]
  linarith

/-- **`SpectralInputNeu` from `lem:LocMatrices` and the windowed Bogoliubov bound**
(FS's `eq:LargeMatricesNew`): the located state's energy loss is *exactly* the shift
`C ↦ C + K` of the `Λ`-coefficient, because `Λ` is affine in that coefficient with the
negative slope `−4πρ²(a v)(ρ(a v)³)^{1/2+η₀}L³` (`lambda_shift_le`). -/
theorem spectralInputNeu_of_locMatricesNeu {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hLM : LocMatricesResidualNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    SpectralInputNeu v J ε₀ η₀ := by
  rcases hLM with ⟨K, hK, hLM⟩
  rcases hB with ⟨C₁, hC₁, hB⟩
  refine ⟨C₁ + K, add_nonneg hC₁ hK, ?_⟩
  intro L hL N hN Φ hlow
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlowH : LowStateNeu v N L J Φ := (lowStateNeu_iff_density hLpos Φ).mpr hlow
  obtain ⟨Psit, hE, hwin⟩ := hLM L hL N hN Φ hlowH
  exact lambda_shift_le (A := a v) (C := C₁) (K := K) (η₀ := η₀) (ρ := dens N L)
    (U := RaylNeu N L v Psit) (V := RaylNeu N L v Φ) hLpos
    (hB L hL N hN Psit hwin) hE

/-- **`UBBNeu` from the two Route-H residuals at the extended class.** -/
theorem UBBNeu_of_locMatricesNeu {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J)
    (hLM : LocMatricesResidualNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    UBBNeu v η₀ :=
  UBBNeu_of_spectralNeu hv ha hε₀ hJ (spectralInputNeu_of_locMatricesNeu hLM hB)

/-! ## 3. The `n₊`-grading datum and its three clauses (FS §7 steps (2)–(5)) -/

/-- **FS §7 step (2)**: the datum of the `n₊`-decomposition of a box state — the block
matrix `𝒜_{ij} = ‖1_{n₊=i}Ψ‖⁻¹‖1_{n₊=j}Ψ‖⁻¹⟨1_{n₊=i}Ψ, H_Λ(μ)1_{n₊=j}Ψ⟩` (an
`nn × nn` Hermitian block matrix supported on the index range `[0,nn-1]`), the unit vector
`ψᵢ = ‖1_{n₊=i}Ψ‖` of sector norms, and the **energy identity**
`⟨ψ,𝒜ψ⟩ = ⟨Ψ, H_Λ(ρ)Ψ⟩` (`= RaylNeu Φ − 8π(a v)ρ²L³`).

The integer spectrum `{0,…,N}` of `n₊ = ΣᵢQᵢ` and the Lagrange spectral projections used
to build `𝒜` are `Work.UBBInputs4.Grading.idem_annihilator` +
`Work.UBBInputs4.Grading.lagrange_spec`. -/
structure GradedDatum (v : ℝ³ → ℝ) (N : ℕ) (L : ℝ) (Φ : CNeu N L) (M : ℕ) where
  /-- The number of blocks (`n₊`-sectors) occurring in `Φ`. -/
  nn : ℕ
  /-- The block matrix `𝒜`. -/
  A : ℤ → ℤ → ℂ
  /-- The vector of sector norms `‖1_{n₊=i}Ψ‖`. -/
  ψv : ℤ → ℂ
  /-- The window length is honoured. -/
  le_nn : M ≤ nn
  /-- `𝒜` is supported on the index range `[0,nn-1] × [0,nn-1]`. -/
  suppA : ∀ i j, A i j ≠ 0 → i ∈ iRange nn ∧ j ∈ iRange nn
  /-- `𝒜` is Hermitian. -/
  herm : ∀ i j, A j i = star (A i j)
  /-- `ψ` is supported on the index range. -/
  suppψ : ∀ j, ψv j ≠ 0 → j ∈ iRange nn
  /-- `ψ` is a unit vector (the norms of the sectors). -/
  unit : normSq (iRange nn) ψv = 1
  /-- **The energy identity**: `⟪ψ,𝒜ψ⟫ = ⟨Ψ, H_Λ(ρ)Ψ⟩`. -/
  energy : qform A (iRange nn) ψv ψv
      = RaylNeu N L v Φ - 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3

namespace GradedDatum

variable {v : ℝ³ → ℝ} {N : ℕ} {L : ℝ} {Φ : CNeu N L} {M : ℕ}

/-- **FS §7 step (3), the band property**: only the supra/infra-diagonals of order `0,1,2`
of `𝒜` are nonzero (the potential changes `n₊` by at most `2`; the kinetic part is
`n₊`-diagonal). -/
def Band (gd : GradedDatum v N L Φ M) : Prop :=
  ∀ k : ℤ, 3 ≤ k → dk gd.A gd.nn gd.ψv k = 0

/-- **FS §7 step (4) = `eq:dvapriori`**: the first two off-diagonal expectations are bounded
by `Kρ²(a v)(ρ(a v)³)^{1/2+η₀}L³`.  FS: *"this is the only place in this paper where an
estimate depends explicitly on `∫v` and not just on `a`"*. -/
def Dv (gd : GradedDatum v N L Φ M) (K η₀ : ℝ) : Prop :=
  |dk gd.A gd.nn gd.ψv 1| + |dk gd.A gd.nn gd.ψv 2|
    ≤ K * (dens N L) ^ 2 * (a v) * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3

/-- **FS §7 step (5), the recombination**: for every unit vector `φ` supported in a window
of `M` consecutive indices, the recombined state

    Ψ̃ = Σᵢ φᵢ ‖1_{n₊=i}Ψ‖⁻¹ 1_{n₊=i}Ψ

(an element of the **extended class** `CNeu N L`, not of `CInfty0Box`) has shifted energy at
most `⟨φ,𝒜φ⟩` and lies in the covariant `n₊`-window `W`. -/
def Recomb (gd : GradedDatum v N L Φ M) (W : ℕ → ℝ → ℝ) : Prop :=
  ∀ (n₀ : ℤ) (φ : ℤ → ℂ), 0 ≤ n₀ → n₀ + (M : ℤ) ≤ (gd.nn : ℤ) →
    (∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (M : ℤ)) → normSq (iRange gd.nn) φ = 1 →
      ∃ Psit : CNeu N L,
        RaylNeu N L v Psit
            ≤ qform gd.A (iRange gd.nn) φ φ + 8 * π * (a v) * (dens N L) ^ 2 * L ^ 3
        ∧ WindowNeu W N L Psit

end GradedDatum

/-- **The `n₊`-grading, clause (2)+(3)**: every low state admits a graded datum with the
band property.  (The bulk of FS §7: the spectral decomposition of `n₊` and the fact that
the Hamiltonian changes `n₊` by at most `2`.) -/
def GradingBlocksNeu (M : ℕ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ : ℝ) : Prop :=
  3 ≤ M ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∃ gd : GradedDatum v N L Φ M, gd.Band

/-- **The `n₊`-grading, clause (4)**: `eq:dvapriori` on every band datum. -/
def GradingDvNeu (M : ℕ) (K : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v) (J ε₀ η₀ : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Band → gd.Dv K η₀

/-- **The `n₊`-grading, clause (5)**: the recombination. -/
def GradingRecombNeu (M : ℕ) (W : ℕ → ℝ → ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (J ε₀ : ℝ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
    ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
      ∀ gd : GradedDatum v N L Φ M, gd.Recomb W

/-- **The `n₊`-grading of the box Hamiltonian at the extended class** (FS §7 steps
(2)–(5)), as the conjunction of the three separately attackable clauses
`GradingBlocksNeu` (steps (2)+(3): the matrix and the band property), `GradingDvNeu`
(step (4), `eq:dvapriori`, the only place `∫v` appears) and `GradingRecombNeu`
(step (5), the recombination with the covariant window). -/
def NPlusGradingNeu (v : ℝ³ → ℝ) (h : ScatSol v) (J : ℝ) (W : ℕ → ℝ → ℝ)
    (ε₀ η₀ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℕ, 3 ≤ M ∧
    GradingBlocksNeu M v h J ε₀ ∧ GradingDvNeu M K v h J ε₀ η₀ ∧
      GradingRecombNeu M W v h J ε₀

/-- The three clauses assemble to the grading residual (one direction of the equivalence
`NPlusGradingNeu ↔ GradingBlocksNeu ∧ GradingDvNeu ∧ GradingRecombNeu`). -/
theorem nPlusGradingNeu_of_clauses {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ K : ℝ}
    {W : ℕ → ℝ → ℝ} {M : ℕ} (hM : 3 ≤ M) (hK : 0 ≤ K)
    (hB : GradingBlocksNeu M v h J ε₀)
    (hD : GradingDvNeu M K v h J ε₀ η₀) (hR : GradingRecombNeu M W v h J ε₀) :
    NPlusGradingNeu v h J W ε₀ η₀ :=
  ⟨K, hK, M, hM, hB, hD, hR⟩

/-- Unpacking of the grading residual: a low state produces a graded datum satisfying all
three clauses. -/
theorem exists_gradedDatum_of_gradingNeu {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hg : NPlusGradingNeu v h J W ε₀ η₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℕ, 3 ≤ M ∧
      ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ →
        ∀ Φ : CNeu N L, LowStateNeu v N L J Φ →
          ∃ gd : GradedDatum v N L Φ M,
            gd.Band ∧ gd.Dv K η₀ ∧ gd.Recomb W := by
  obtain ⟨K, hK, M, hM, hblocks, hdv, hrecomb⟩ := hg
  obtain ⟨hM3, hblocks⟩ := hblocks
  obtain ⟨hK0, hdv⟩ := hdv
  refine ⟨K, hK, M, hM3, fun L hL N hN Φ hlow => ?_⟩
  obtain ⟨gd, hband⟩ := hblocks L hL N hN Φ hlow
  exact ⟨gd, hband, hdv L hL N hN Φ hlow gd hband,
    hrecomb L hL N hN Φ hlow gd⟩

/-- **`lem:LocMatrices` at the extended class from the `n₊`-grading** — the composition of
the (proved) Lieb–Solovej matrix theorem `ls_localisation_band2` with the grading datum.
The constant `500 K + 4π + 1` is the absorption of the Lieb–Solovej error
`100 M⁻²(|d₁| + 4|d₂|)` into the FS exponent `(ρ(a v)³)^{1/2+η₀}` (all the arithmetic is
proved here). -/
theorem locMatricesResidualNeu_of_gradingNeu {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (ha : 0 ≤ a v) (hg : NPlusGradingNeu v h J W ε₀ η₀) :
    LocMatricesResidualNeu v h J W ε₀ η₀ := by
  obtain ⟨K, hK0, M, hM3, hdata⟩ := exists_gradedDatum_of_gradingNeu hg
  refine ⟨500 * K + 4 * π + 1, by positivity, fun L hL N hN Φ hlow => ?_⟩
  obtain ⟨gd, hband, hdv', hrecomb⟩ := hdata L hL N hN Φ hlow
  obtain ⟨n₀, h0, h1, φ, hsupp, hnorm, hineq⟩ :=
    ls_localisation_band2 gd.A gd.nn M gd.ψv hM3 gd.le_nn gd.suppA gd.herm gd.suppψ
      gd.unit hband
  obtain ⟨Psit, henergy, hcn⟩ := hrecomb n₀ φ h0 h1 hsupp hnorm
  set Y : ℝ := (dens N L) ^ 2 * (a v) * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3
    with hYdef
  have hρ0 : (0 : ℝ) ≤ dens N L := by
    unfold dens
    positivity
  have hY : 0 ≤ Y := by
    rw [hYdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) ha)
      (Real.rpow_nonneg (mul_nonneg hρ0 (pow_nonneg ha 3)) _)) (by positivity)
  have hdvY : |dk gd.A gd.nn gd.ψv 1| + |dk gd.A gd.nn gd.ψv 2| ≤ K * Y := by
    have hKY : K * Y = K * dens N L ^ 2 * a v * (dens N L * a v ^ 3) ^ (1 / 2 + η₀) * L ^ 3 := by
      rw [hYdef]
      ring
    rw [hKY]
    exact hdv'
  have hstep : (100 / (M : ℝ) ^ 2) * (|dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2|)
      ≤ 4 * π * (dens N L) ^ 2 * (a v) * (500 * K + 4 * π + 1)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3 := by
    have h1 : |dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2| ≤ 5 * (K * Y) := by
      linarith [hdvY, abs_nonneg (dk gd.A gd.nn gd.ψv 1), abs_nonneg (dk gd.A gd.nn gd.ψv 2)]
    have hA : (100 / (M : ℝ) ^ 2) * (|dk gd.A gd.nn gd.ψv 1| + 4 * |dk gd.A gd.nn gd.ψv 2|)
        ≤ (100 / (M : ℝ) ^ 2) * (5 * (K * Y)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h2 : (100 / (M : ℝ) ^ 2) * (5 * (K * Y)) ≤ 100 * (5 * (K * Y)) := by
      have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
      have hle : 100 / (M : ℝ) ^ 2 ≤ 100 := by
        rw [div_le_iff₀ hMpos]
        nlinarith [sq_nonneg (M : ℝ), hM1]
      exact mul_le_mul_of_nonneg_right hle (by nlinarith [hY, hK0])
    have h3 : 100 * (5 * (K * Y)) ≤ 4 * π * Y * (500 * K + 4 * π + 1) := by
      have hbase : 500 * K ≤ 4 * π * (500 * K + 4 * π + 1) := by
        nlinarith [hK0, Real.pi_gt_three, sq_nonneg π]
      have hmul : 500 * K * Y ≤ 4 * π * (500 * K + 4 * π + 1) * Y :=
        mul_le_mul_of_nonneg_right hbase hY
      linarith [hmul]
    have h4 : 4 * π * Y * (500 * K + 4 * π + 1)
        = 4 * π * (dens N L) ^ 2 * (a v) * (500 * K + 4 * π + 1)
            * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3 := by
      rw [hYdef]
      ring
    linarith
  refine ⟨Psit, ?_, hcn⟩
  linarith [gd.energy, hineq, henergy, hstep]

/-! ## 4. The end-to-end chain (Route H at the extended class) -/

/-- **`UBBNeu` from the `n₊`-grading and the windowed Bogoliubov bound** — Route H with the
trial class repaired. -/
theorem UBBNeu_of_gradingNeu {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hg : NPlusGradingNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    UBBNeu v η₀ :=
  UBBNeu_of_locMatricesNeu hv ha hε₀ hJ (locMatricesResidualNeu_of_gradingNeu ha hg) hB

/-- **The delivered `UBB` (Dirichlet box bound) from the extended-class grading** — the
bridge that keeps every `CInfty0Box` consumer working (`eNeu ≤ boxEnergy`). -/
theorem UBB_of_gradingNeu {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (ha : 0 ≤ a v)
    (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀) (hg : NPlusGradingNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_UBBNeu hv hv1 (UBBNeu_of_gradingNeu hv ha hJ hε₀ hg hB)

/-- **The paper's `hpres` from the shortest Route-H hypothesis list at the extended class**
(the round-4 deliverable): `NPlusGradingNeu + BogoliubovWindowedNeu ⟹ hpres`, through the
delivered grand-canonical interface, with the state class of FS §7. -/
theorem hpres_of_gradingNeu {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hg : NPlusGradingNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBNeu hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBBNeu_of_gradingNeu hv (le_of_lt hav) hJ hε₀ hg hB)


/-! ## 4bis. The window reconciliation (FS use *different* windows for the two layers) -/

/-- The localisation residual is **covariant** in the window: a bigger `W` is a weaker
conclusion. -/
theorem locMatricesResidualNeu_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW' : ∀ N L, W N L ≤ W' N L)
    (hLM : LocMatricesResidualNeu v h J W ε₀ η₀) :
    LocMatricesResidualNeu v h J W' ε₀ η₀ := by
  rcases hLM with ⟨K, hK, hLM⟩
  refine ⟨K, hK, fun L hL N hN Φ hlow => ?_⟩
  obtain ⟨Psit, hE, hwin⟩ := hLM L hL N hN Φ hlow
  exact ⟨Psit, hE, windowNeu_mono hWW' hwin⟩

/-- The Bogoliubov residual is **contravariant** in the window: a bigger `W` is a weaker
hypothesis, hence a stronger statement. -/
theorem bogoliubovWindowedNeu_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hWW' : ∀ N L, W N L ≤ W' N L)
    (hB : BogoliubovWindowedNeu v h J W' ε₀ η₀) :
    BogoliubovWindowedNeu v h J W ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  refine ⟨C, hC, fun L hL N hN Φ hwin => ?_⟩
  exact hB L hL N hN Φ (windowNeu_mono hWW' hwin)

/-- **The two residuals can be consumed at *different* windows** (as in FS, where
`lem:LocMatrices` produces the `n₊`-window and §9–11 is applied at the a-priori window):
any comparable pair `W ≤ W'` works. -/
theorem UBBNeu_of_locMatricesWindows {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a v) (hε₀ : 0 < ε₀) (hJ : lhyC ≤ J)
    (hWW' : ∀ N L, W N L ≤ W' N L)
    (hLM : LocMatricesResidualNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W' ε₀ η₀) :
    UBBNeu v η₀ :=
  UBBNeu_of_locMatricesNeu hv ha hε₀ hJ
    (locMatricesResidualNeu_mono_window (W := W) (W' := W') hWW' hLM) hB

/-- The same at the paper's `hpres`. -/
theorem hpres_of_gradingNeuWindows {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 ≤ R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {h : ScatSol v}
    {J ε₀ η₀ η K : ℝ} {W W' : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hWW' : ∀ N L, W N L ≤ W' N L)
    (hLM : LocMatricesResidualNeu v h J W ε₀ η₀)
    (hB : BogoliubovWindowedNeu v h J W' ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBBNeu hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBBNeu_of_locMatricesWindows hv (le_of_lt hav) hε₀ hJ hWW' hLM hB)

end Work.UBBInputs4
