import ChallengeDeps
import Submission.GCBoxBound
import Submission.Symmetry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseTop` — the finite-volume LHY target `HBoxG` (area root)

This is the **area root** of `Submission/Work/BoseTop`: the top-level interface
between the corpus (whose only remaining gap is the pressure-level
LHY-Background bound `hpres` inside the challenge theorem) and the future
Fournais--Solovej finite-volume analysis (FS §5--§11).

## The target

Audit 2026-10-03 nodes `R0` + `G`.  The old route through a *canonical*
per-box statement quantified over all `L ≥ 1` and all `N` with the chemical
potential tied to the sector (`μ := N/L³`) is DEAD: it is refuted at `N = 1`
by the constant state.  FS instead fix `μ`, tie the box side to `μ`,
`ℓ = K_ℓ (μ a)^{-1/2}`, leave the particle number `n` free and use
`ρa³`-dependent parameters.

The single remaining input in the corpus language is the **finite-volume
LHY-Background bound**, eventually in `L`, at the FS chemical potential
`μ = 8π a v·ρ` and truncation density `2ρ`:

* `HBoxG v η₀ Cw` (all-functions form, built from the corpus `boxEnergy` via
  `gcDensity`) — this is the input of the CLOSED interface
  `Submission.BoseGases.hpres_of_gcTwoTerm` (`Submission/GCBoxBound.lean`);
* `HBoxGSym v η₀ Cw` — the same statement with the *symmetric* (bosonic)
  grand-canonical energy `symBoxEnergy` replacing `boxEnergy`.  This is the
  form in which FS's own analysis (and the corpus sector machinery,
  `Symmetry.SymBox`) naturally produces the bound; the transfer from the
  symmetric to the full form is the bosonic reduction `symBoxReduction`
  (node `S`, stated in the corpus as `Submission.SymmetryGoal`).

`HBoxGTarget v` bundles the two numerical side conditions that the audit's
parameter assembly produces (`1/2000 < η₀`, `η₀ ≤ 1/2`, `0 ≤ Cw`).

## What this module provides

* the definitions `gcSetSym`/`gcBoxSym`/`gcDensitySym`, `symBoxReduction`,
  `HBoxG`, `HBoxGSym`, `HBoxGTarget`, `HBoxGSymTarget`;
* the elementary symmetric energy facts `symQuot_nonneg`,
  `symBoxEnergy_nonneg`;
* the set-theoretic comparison `gcBoxSym_le_gcBox`,
  `gcDensitySym_le_gcDensity` and hence `HBoxG_of_HBoxGSym`,
  `HBoxGTarget_of_HBoxGSymTarget`;
* the `a v = 0` sanity branch `HBoxG_of_av_zero`, `HBoxGTarget_of_av_zero`
  (so `HBoxGTarget` is inhabited whenever the scattering length vanishes —
  the target is not vacuous).

The top reduction (the challenge theorem from `HBoxGTarget`) lives in
`Submission/Work/BoseTop/Reduction.lean`; the per-`N`/per-state reductions
that the C/B nodes feed into live in `Submission/Work/BoseTop/PerN.lean`.
-/

noncomputable section

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open Submission.BoseGases
set_option autoImplicit false

namespace Work.BoseTop

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The challenge's error exponent

The exponent `η` of the challenge statement is `1/2000` (a `Submission`-side
definition).  It is repeated here as a *real* constant: writing the literal
`1 / 2 + 1 / 2000` inside an exponent position of a displayed term would
elaborate at type `ℕ` (the trap), whereas `1 / 2 + etaBose` cannot. -/

/-- The challenge's error exponent, `η = 1/2000`. -/
noncomputable def etaBose : ℝ := 1 / 2000

lemma etaBose_pos : 0 < etaBose := by unfold etaBose; norm_num

lemma etaBose_eq : etaBose = 1 / 2000 := rfl

/-! ## The symmetric grand-canonical bookkeeping -/

/-- Admissible particle numbers with the *symmetric* energy: the set of values
`symBoxEnergy N L v − μ N` over `N ≤ ρmax·L³`. -/
def gcSetSym (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : Set ℝ :=
  {y : ℝ | ∃ N : ℕ, gcAdmissible ρmax L N ∧ y = symBoxEnergy N L v - μ * (N : ℝ)}

/-- The truncated symmetric grand-canonical ground-state energy of a box of
side `L` (the bosonic analogue of `gcBox`). -/
noncomputable def gcBoxSym (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : ℝ :=
  sInf (gcSetSym v μ ρmax L)

/-- The symmetric grand-canonical energy density of a box of side `L`. -/
noncomputable def gcDensitySym (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : ℝ :=
  gcBoxSym v μ ρmax L / L ^ 3

/-- The bosonic (Perron--Frobenius) reduction, as a hypothesis: for `0 ≤ v` the
ground-state energy over the symmetric trial space is no larger than the one
over all trial functions.  Stated exactly as in `Submission/SymmetryGoal.lean`
(node `S` of the audit), but as a predicate here so that the top reduction can
be made conditional on it without importing a module that carries a proof
obligation. -/
def symBoxReduction (v : ℝ³ → ℝ) : Prop :=
  ∀ (N : ℕ) (L : ℝ), 0 < L → symBoxEnergy N L v ≤ boxEnergy N L v

/-! ## The two forms of the finite-volume LHY target -/

/-- **The single remaining research target** (audit nodes `R0`+`G`): the
Fournais--Solovej finite-volume LHY-Background bound at the chemical potential
`μ = 8π a v·ρ` and truncation density `2ρ`, *eventually in the box side* `L`.

With `c := 128/(15√π)` and `gcTwoTerm A Cw s ρ := 4πAρ²(−1 + c√(ρA³) − Cw(ρA³)^s)`,
this says: for every small density `ρ` there is `L₀ ≥ 1` such that for all
`L ≥ L₀` the truncated grand-canonical density of the corpus box energy
dominates `gcTwoTerm (a v) Cw (1/2+η₀) ρ`.

Note the two sanity requirements of the audit: `ρ` is *fixed* (the chemical
potential is `8π a v·ρ`, not tied to the particle number), and `L₀` is allowed
to depend on `ρ` (no hypothesis of the shape `∀ L ≥ 1, R ≤ L·c`). -/
def HBoxG (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤ gcDensity v (8 * π * a v * ρ) (2 * ρ) L

/-- The **symmetric (bosonic) form** of `HBoxG`: the same bound with the corpus
`symBoxEnergy` in place of `boxEnergy`.  This is the form produced by FS's own
§5--§11 analysis (their trial states are bosonic) and by the corpus sector
machinery (`Symmetry.SymBox`); `HBoxG_of_HBoxGSym` transfers it to `HBoxG`
using the bosonic reduction `symBoxReduction`. -/
def HBoxGSym (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ ≤ gcDensitySym v (8 * π * a v * ρ) (2 * ρ) L

/-- The audit's parameter bundle: the finite-volume target holds for SOME
admissible exponent `η₀ > 1/2000` (strictly larger than the challenge's `η`,
so that the coefficient absorption `(ρa³)^{η₀−η} → 0` works) and SOME
nonnegative coefficient `Cw`.  `η₀ ≤ 1/2` is the FS window. -/
def HBoxGTarget (v : ℝ³ → ℝ) : Prop :=
  ∃ η₀ Cw : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ Cw ∧ HBoxG v η₀ Cw

/-- The symmetric-sector version of `HBoxGTarget`. -/
def HBoxGSymTarget (v : ℝ³ → ℝ) : Prop :=
  ∃ η₀ Cw : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ Cw ∧ HBoxGSym v η₀ Cw

/-! ## The per-state forms handed to the FS §5--§11 analysis

The two predicates below are the *per-block, per-state* canonical forms of the
targets: no grand-canonical infimum, no density normalisation.  They are the
shape in which the deeper nodes deliver the bound (for every admissible
particle number `N` and every trial state), and the shape from which the
grand-canonical targets follow by an infimum over `N` (and over `Ψ`). -/

/-- **The handoff predicate (all functions)**: for every small density `ρ`,
every large box side `L`, every admissible particle number `N` (`N ≤ 2ρL³`) the
corpus box energy satisfies the canonical two-term inequality
`gcTwoTerm·L³ ≤ E(N,L) − 8π a v ρ·N`.

By `PerN/HBoxG_of_HBoxGState` this implies `HBoxG`, so *this* is what a
prover of the finite-volume target needs to establish.

Note that `N = 0` is included (`boxEnergy 0 L v = 0`), where the inequality
reads `gcTwoTerm (a v) Cw (1/2+η₀) ρ ≤ 0`; that is true for small `ρ`
(`Util/eventually_gcTwoTerm_nonpos`), so the predicate is not obstructed by the
empty box. -/
def HBoxGState (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ,
    gcAdmissible (2 * ρ) L N →
      gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ * L ^ 3 ≤
        boxEnergy N L v - (8 * π * a v * ρ) * (N : ℝ)

/-- **The handoff predicate (symmetric states)**: for every small density `ρ`,
every large box side `L`, every admissible particle number `N` (`N ≤ 2ρL³`) and
every *symmetric* (bosonic) trial state `Ψ` the corpus Rayleigh quotient of `Ψ`
dominates `gcTwoTerm·L³ + 8π a v ρ·N`.

This is the shape in which FS's localised analysis (node `C`, comparing the
big box with the localised box of side `ℓ = K_ℓ (μ a)^{-1/2}` at
`μ := 8π a v ρ`, plus node `B` bounding the localised energy) delivers the
finite-volume bound; `PerN/HBoxGSym_of_HBoxGSymState` converts it into
`HBoxGSym` by taking the infimum over `Ψ` and then over `N`.

Note that `N = 0` is included (`symBoxEnergy 0 L v = 0`, `symQuot 0 L v Ψ = 0`),
where the inequality reads `gcTwoTerm (a v) Cw (1/2+η₀) ρ ≤ 0`; that holds for
small `ρ` (`Util/eventually_gcTwoTerm_nonpos`), so the predicate is not
obstructed by the empty box. -/
def HBoxGSymState (v : ℝ³ → ℝ) (η₀ Cw : ℝ) : Prop :=
  ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ N : ℕ,
    gcAdmissible (2 * ρ) L N → ∀ Ψ : SymBox N L,
      gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ * L ^ 3 + (8 * π * a v * ρ) * (N : ℝ) ≤
        symQuot N L v Ψ

/-! ## Elementary symmetric energy facts -/

/-- Nonnegativity of the symmetric Rayleigh quotient for `0 ≤ v`. -/
lemma symQuot_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : SymBox N L) : 0 ≤ symQuot N L v Ψ := by
  rw [← fullQuot_symQuot v Ψ]
  exact fullQuot_nonneg hL hv Ψ.toCInfty0Box

/-- Nonnegativity of the symmetric box energy for `0 ≤ v`. -/
lemma symBoxEnergy_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    0 ≤ symBoxEnergy N L v := by
  haveI : Nonempty (SymBox N L) := nonempty_SymBox N hL
  change 0 ≤ ⨅ Ψ : SymBox N L, symQuot N L v Ψ
  exact le_ciInf (fun Ψ => symQuot_nonneg hL hv Ψ)

/-- Nonemptiness of the symmetric value set (`N = 0` is always admissible). -/
lemma gcSetSym_nonempty {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hρmax : 0 ≤ ρmax) (hL : 0 ≤ L) :
    (gcSetSym v μ ρmax L).Nonempty := by
  have h0 : gcAdmissible ρmax L 0 := by
    dsimp [gcAdmissible]
    simpa using mul_nonneg hρmax (pow_nonneg hL 3)
  exact ⟨symBoxEnergy 0 L v - μ * ((0 : ℕ) : ℝ), 0, h0, rfl⟩

/-! ## From the symmetric to the full grand-canonical energy -/

/-- The symmetric grand-canonical energy is dominated by the corpus
grand-canonical energy, *given* the bosonic reduction `symBoxEnergy ≤ boxEnergy`
(the direction proved in node `S`). -/
theorem gcBoxSym_le_gcBox {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hred : symBoxReduction v)
    {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax) (hL : 0 < L) :
    gcBoxSym v μ ρmax L ≤ gcBox v μ ρmax L := by
  have hbdd : BddBelow (gcSetSym v μ ρmax L) := by
    refine ⟨-(μ * (ρmax * L ^ 3)), ?_⟩
    rintro y ⟨N, hN, rfl⟩
    have hE : 0 ≤ symBoxEnergy N L v := symBoxEnergy_nonneg hL hv
    have hNad : (N : ℝ) ≤ ρmax * L ^ 3 := hN
    have hmul : μ * (N : ℝ) ≤ μ * (ρmax * L ^ 3) := mul_le_mul_of_nonneg_left hNad hμ
    linarith
  unfold gcBoxSym gcBox
  refine sInf_le_sInf_of_le (gcSet_nonempty (v := v) (μ := μ) hρmax hL.le) hbdd ?_
  rintro y ⟨N, hN, rfl⟩
  exact ⟨symBoxEnergy N L v - μ * (N : ℝ), ⟨N, hN, rfl⟩, sub_le_sub_right (hred N L hL) _⟩

/-- Density form of `gcBoxSym_le_gcBox`. -/
theorem gcDensitySym_le_gcDensity {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hred : symBoxReduction v)
    {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax) (hL : 0 < L) :
    gcDensitySym v μ ρmax L ≤ gcDensity v μ ρmax L := by
  unfold gcDensitySym gcDensity
  exact div_le_div_of_nonneg_right (gcBoxSym_le_gcBox hv hred hμ hρmax hL) (pow_nonneg hL.le 3)

/-- The symmetric-sector target implies the all-functions target, given the
bosonic reduction. -/
theorem HBoxG_of_HBoxGSym {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hred : symBoxReduction v)
    (hav : 0 ≤ a v) {η₀ Cw : ℝ} (h : HBoxGSym v η₀ Cw) : HBoxG v η₀ Cw := by
  filter_upwards [h, self_mem_nhdsWithin] with ρ hρ hρpos
  rcases hρ with ⟨L₀, hL₀1, hL₀⟩
  refine ⟨L₀, hL₀1, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hL₀1 hL)
  have hρ0 : 0 < ρ := hρpos
  have hμ : 0 ≤ 8 * π * a v * ρ := mul_nonneg (mul_nonneg (by positivity) hav) hρ0.le
  have hρmax : 0 ≤ 2 * ρ := by linarith
  exact le_trans (hL₀ L hL) (gcDensitySym_le_gcDensity hv hred hμ hρmax hLpos)

/-- The symmetric-sector parameter bundle implies the target bundle. -/
theorem HBoxGTarget_of_HBoxGSymTarget {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hred : symBoxReduction v)
    (hav : 0 ≤ a v) (h : HBoxGSymTarget v) : HBoxGTarget v := by
  rcases h with ⟨η₀, Cw, h1, h2, h3, h4⟩
  exact ⟨η₀, Cw, h1, h2, h3, HBoxG_of_HBoxGSym hv hred hav h4⟩

/-! ## The vanishing-scattering-length branch (the target is inhabited) -/

/-- When the scattering length vanishes, `gcTwoTerm 0 Cw s ρ = 0` while the
corpus grand-canonical density is nonnegative, so the finite-volume target
holds unconditionally.  This is the `a v = 0` branch of the audit's node `G`;
it shows in particular that `HBoxGTarget` is not vacuous. -/
theorem HBoxG_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0) {η₀ Cw : ℝ} :
    HBoxG v η₀ Cw := by
  filter_upwards [self_mem_nhdsWithin] with ρ hρpos
  have hρ0 : 0 < ρ := hρpos
  have hρmax : 0 ≤ 2 * ρ := by linarith
  refine ⟨1, le_rfl, fun L hL1 => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hgc : 0 ≤ gcBox v 0 (2 * ρ) L := by
    have h := gcBox_ge (v := v) (μ := 0) (ρmax := 2 * ρ) (L := L)
      (by norm_num) hρmax hLpos hv
    simpa using h
  have hd : 0 ≤ gcDensity v 0 (2 * ρ) L := by
    unfold gcDensity
    exact div_nonneg hgc (pow_nonneg hLpos.le 3)
  have hlhs : gcTwoTerm (a v) Cw (1 / 2 + η₀) ρ = 0 := by
    rw [hav]
    unfold gcTwoTerm
    ring
  have hμ : 8 * π * a v * ρ = 0 := by
    rw [hav]
    ring
  rw [hlhs, hμ]
  exact hd

/-- The vanishing-scattering-length branch of the parameter bundle. -/
theorem HBoxGTarget_of_av_zero {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hav : a v = 0) :
    HBoxGTarget v :=
  ⟨1 / 4, 0, by norm_num, by norm_num, le_rfl, HBoxG_of_av_zero hv hav⟩

end Work.BoseTop
