import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.B3.seed_half
import Submission.Work.Diff.STE.Lead.gal_uniform_assembly
import Submission.Work.Diff.STE.Lead.GalTame.galerkin_trapped_strong
import Submission.Work.Diff.STE.Lead.GalTame.hapr_of_aPrioriL2
import Submission.Work.Diff.STE.Lead.GalTame.deTurck_low_energy
import Submission.Work.Diff.STE.Lead.GalTame.gardingSharp_hG_of_jet
import Submission.Work.Diff.STE.Lead.GalTame.gardingSharp
import Submission.Work.Diff.STE.Lead.GalTame.pdVec_defect_sharp
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Lead.Gal.galE_comm

/-! Guidance from the project lead (the requester):

CONTEXT: last layer of short_time_existence (owner H10, Diff/STE). The lead dispatched these pieces top-level so they run in parallel.
Vocabulary: Submission/Work/Diff/STE/B3/Comp.lean (R, Rper, CPair, BPair, BNorm, Rstar, STruncR, J), B3/Data.lean (B3Data: x₀, χ, ζ, e, dens,
psi), D/* (Galerkin, genMap, jSym, addSec, deTurckSec, ChartData, smetOf), and the lead's Submission/Diff/STEGal.lean (galState, IsGalSol,
GalUniform). REUSE the PROVED Layer A toolkit (Submission/Work/Diff/STE/*.lean; LayerA.lean lists it): CSq_trunc_le,
CSq_trunc_sub_le, friedrichs_commutator, CSq_period_comp_arg_le, CSq_conv_tame_le, CSq_comp_le, garding_vec_uniform,
gronwall_linear_bound, norm_seriesFun_le (Sobolev), CSq_tail_le (compactness), eq_zero_of_fourierCoeff_eq_zero, BPair_J_self,
BPair_Rstar, J_finite_rank, R_Rstar_expansion2 (chart transfer). Read DESIGN.md (sessions 6–8) first. Do not re-prove anything listed.
If a statement here is false as stated (e.g. a missing hypothesis on ρ or on B3Data), declare_false with the precise reason; the lead fixes it.
NOTE: this REPLACES Diff/STE/Lead/gal_uniform (H2375 correctly showed the ∀ ε ∈ (0,1] form false at ε = 1). GalUniform is now the
∃ ε₀ > 0, ∀ ε ∈ (0, ε₀] form. H2375's files under Submission/Work/Diff/STE/Lead/ are available; reuse anything proved there.
ROUTE (gal_uniform: the uniform energy bound + positivity persistence + continuation; the analytic core D2/D3).
1. Local Galerkin solution: the ODE c' = (coefficients of J P(J u)) on the finite-dimensional range (J_finite_rank / genMap) is
   locally Lipschitz while J u stays positive (Picard–Lindelöf, as in H10's galSol2_exists / galODE_local_exists). It continues as long
   as |c| stays bounded and J u stays uniformly positive.
2. Energy at a level k0 > n/2 + 3: d/dt BNorm k0 (u) = 2⟨u, J P(J u)⟩_k0 (hasDerivAt_ENormB in D/EnergyDeriv.lean).
   Move J across with BPair_J_self plus the Friedrichs commutator (friedrichs_commutator + chart cross terms, uniform in ε).
   The scalar principal part of P (DeTurck structure, C1 proved: secOp + pN) gives Gårding (garding_vec_uniform):
   −λ‖Ju‖²_{k0+1} + C(‖u‖_k0, λ⁻¹). The tame/Moser estimates (CSq_conv_tame_le, CSq_comp_le) handle pN.
   Grönwall (gronwall_linear_bound): bound B on an interval τ₀ depending only on BNorm k0 g₀ and on the positivity of g₀.
3. Positivity margin: |u(t) − g₀|_{C⁰} ≤ C t from the time-derivative bound and Sobolev, so J u ≥ lam·g₀ for t ≤ τ₀ (shrink τ₀).
   At t = 0: J ρ ε g₀ → g₀ in BNorm k for k large (hJT), hence uniformly (Sobolev). g₀ is uniformly positive on compact M.
   So there is ε₀ > 0 with J ρ ε g₀ ≥ (lam₀/2)·g₀ for ε ≤ ε₀. GalUniform (FIXED 2026-10-02) asks only for ε ∈ (0, ε₀]: choose ε₀ here.
4. Higher levels on the SAME interval: the lead's level-by-level linear estimate (no Gagliardo–Nirenberg). For k ≥ k0,
   d/dt BNorm (k+1) ≤ C(B k)(1 + BNorm (k+1)), since in a product of total order ≤ k+3 at most one factor has order > (k+3)/2 ≤ k − n/2 − 1;
   the others are bounded in sup norm by Sobolev at level k. Induct, Grönwall: B (k+1).
5. With these bounds |c| stays bounded, so the solution continues to [0,τ₀] (step 1). Output c with IsGalSol on [0,τ₀].
File 1–5 as separate exact sub-lemmas at once (the commutator estimate as its own lemma).
-/

namespace Work.Diff.STE.Lead

/-! ## State of the proof of `gal_uniform_v2` (progress note, 2026-10-02 late)

**Read this before touching the file.**

### The reduction (proved, in `Gal/Prelude.lean` and `Gal/Prelude2.lean`)

`GalUniform` asks for `ε₀, τ₀ > 0`, `lam > 0`, `B : ℕ → ℝ` such that for every `ε ∈ (0, ε₀]` there
is a curve `c` with `IsGalSol hLC D ρ ε τ₀ c`, `∀ k, D.BNorm k (galState D ε (c t)) ≤ B k` and
`lam · g₀.inner ≤ D.J ρ ε (galState D ε (c t))` on `[0, τ₀]`.

The scheme is the *span form* `c' = galVF2 hLC D ρ ε hε hρ0 c` of `u' = J ρ ε (P (J ρ ε u))`:

* `genMap D ε (galVF2 … c) = D.J ρ ε (P (u~(c)))` with `u~(c) = J ρ ε (galState D ε c)`
  (`Work.Diff.STE.Lead.genMap_galVF2`);
* `galVF2` is *total* (it is `0` off the positivity region of `u~(c)`) and **locally Lipschitz on the
  positivity region** (`Gal/galVF2_lipschitz_on_pos`);
* `Work.Diff.STE.Lead.isGalSol_of_galVF2` (now in `Gal/Prelude2.lean`) converts
  `c' = galVF2 … c` + `c 0 = 0` + positivity of `u~(c)` into `IsGalSol` (using proof-irrelevance of
  the DeTurck section, `deTurckSec_congr`, because `IsGalSol` quantifies over the proof arguments);
* `galE D k ε c = D.ENormB k (galState D ε c) + D.ENormB 0 (galState D ε c)` is the energy
  (`Gal/Prelude.lean`).

**Import-cycle warning.** `hasDerivWithinAt_galState`, `deTurckSec_congr`, `isGalSol_of_galVF2` used
to live in THIS file; they were moved verbatim to `Diff/STE/Lead/Gal/Prelude2.lean` so that the
trapping/a-priori modules can use them *without* importing this file.  This file may therefore
import any `GalTame` module built on `Prelude2`; a module that imports *this* file can never be

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
imported here.  (The stray `import … Lead.gal_uniform_v2` at the head of
`GalTame/galerkin_trapped_solution.lean` is vestigial — it uses nothing from this file — but it is
what made a *clean* restatement necessary; see below.)

### The tame (`L²`) interface (replaces the old pointwise `hjet` interface)

The old interface asked for **pointwise** `pdVec`-jets of the chart matrix `D.mat i h c d` up to
order `k+1`; those are *not* derivable from a level-`k` energy bound
(`B3/mat_jet_bound_of_energy` gives order-`m` jets only from `ENormB k₀ h` with `2m + n < 2k₀`), so
it was not instantiable.  The replacement, all under `Diff/STE/Lead/GalTame/`:

| module | content | status |
|---|---|---|
| `Defs` | `GardDataL2` (tame transport data: `L²` bounds on `∂^m A` for `m ≤ k`, sup bounds on `A`, `∂A`, residual and low-order energies bounded by `C(1 + D.ENormB (k+1) h)`) | proved |
| `Level`, `ENormB_mono_level` | Poincaré level conversion `ENormB m h ≤ C ENormB k h` (`1 ≤ m ≤ k`) | proved |
| `galE_apriori_L2` | **the a priori estimate**: `galE k ε (c t) ≤ (galE k ε (c 0) + 1) e^{C t} - 1`, `C` independent of `ε` and of the level-`k` energy | proved |
| `gardingSharp` | sharp Gårding: `ENormB_pair k (P h) h ≤ -(lam'/2) ENormB (k+1) h + Cg (1 + ENormB k h)` | proved (takes the defect `hDefSharp` as a hypothesis) |
| `pdVec_defect_sharp` | the sharp `L²` defect `‖[∂^k, A∂∂]u‖ ≤ C S²(1 + KA + Q1)` = `hDefSharp` | **in flight** |
| `gardingAssemblyL2` | Gårding with a `B`-dependent constant | proved |
| `GardDataL2_of_tame` | `B3/transport_deTurck_tame` ⇒ `GardDataL2` | proved |
| `galerkin_trapped_solution` | trapping + uniform Picard–Lindelöf step + gluing ⇒ `∃ τ₀ > 0`, per-`ε` `IsGalSol` on `[0, τ₀]` with margin `1/4` and `galE k₀ ≤ B`, taking the a priori estimate `hapr` as a hypothesis | **in flight** (imports this file ⇒ must be restated; a clean copy `galerkin_trapped_solution_clean` is being proved) |

**The `J`-commutator.** `galE_apriori_L2` needs
`|ENormB_pair k (J f) u − ENormB_pair k f (J u)| ≤ C √(ENormB (k-1) f + ENormB 0 f) √(ENormB k u)`,
i.e. `Work.Diff.STE.Lead.Gal.galE_comm` / `Diff/STE/B3/ENormB_pair_J_commutator_v2`.  This is the
last big *analytic* gap; it is being proved via the `B3/SymCalc*` route (flat Friedrichs gain +
cross-chart transfer), and is *not* owned by this file.

### ⚑ The assembly is DONE: see `Diff/STE/Lead/gal_uniform_assembly.lean`

**`Work.Diff.STE.Lead.galUniform_of`** in `Submission/Work/Diff/STE/Lead/gal_uniform_assembly.lean`
proves `GalUniform hLC D ρ` from explicit hypotheses, and it **builds, sorry-free**:

* `trapBounds` (proved there): from the trap bound `galE D k₀ ε c ≤ B` alone it produces `K > 0` and
  `B₀ ≥ 0` with the pointwise upper bound `D.J ρ ε (galState D ε c) ≤ K · g₀` and the level-`k₀`
  energy bound of the *mollified* state — exactly the `hub` and the last hypothesis of
  `galE_apriori_L2`, uniformly in `ε ∈ (0, 1]`;
* `isGalSol_mono` (proved there): `IsGalSol` is monotone in the interval (so the output interval is
  `τ₀/2`, which makes the *closed* endpoint of `GalUniform` available);
* `galUniform_of`: the whole level-by-level assembly on the single interval `τ₀/2`, with
  `B k := max (Cβ k · ((ENormB k g₀.inner + ENormB 0 g₀.inner + 1) · exp (ClevAll k · τ₀) − 1))
                 (Cβ k · ((CW + 3) · B))`
  (`Cβ k` from `B3/BNorm_le_ENormB_unif`, `ClevAll` the level-`k` Grönwall constant, `CW` the
  Poincaré constant of `GalTame/ENormB_mono_level`).

Its hypotheses (all *conclusions* of the lemmas below) are:

| hypothesis of `galUniform_of` | supplied by |
|---|---|
| `hJN` | the target's own `hJN` (verbatim) |
| `εs, hseed` | `Submission/Work/Diff/STE/B3/seed_margin` with `hJT` (`lam = 1/2`) — **proved, clean** |
| `k₀, hk₀, hk₀4` | `k₀ := Module.finrank ℝ E + 13` |
| `B, hB` | `B := D.ENormB k₀ g₀.inner + D.ENormB 0 g₀.inner + 1` |
| `hGS` | `GalTame/gardingSharp` (with the defect), i.e. `GardingSharpData` |
| `hComm` | `Work.Diff.STE.Lead.Gal.galE_comm`, i.e. `CommData` |
| `hGk` | `GalTame/gardingSharp_hG_of_jet` (**proved**) applied to `hGS` |
| `hLowk` | `Work.Diff.STE.Lead.lowEnergyData_of` (in the assembly module) applied to `GalTame/deTurck_low_energy` — *no* `TransportData`/`GardDataL2_of_tame` is needed any more |
| `hApr` | `GalTame/hapr_of_aPrioriL2` (with `hGk k₀`, `hLowk k₀`, `hComm k₀`, `hJN`) — **proved, clean** |
| `hTrap` | `GalTame/galerkin_trapped_strong` (with `hseed`, and the `hTrap` hypothesis of `galUniform_of` is already *abstracted* over `Cof` and the `hapr`, so the conversion `ε ≤ 1 ↦ ε ≤ min εs 1` is done inside `galUniform_of`) |

So the file `gal_uniform_v2.lean` is finished as soon as those providers exist; the final proof is

```lean
  obtain ⟨εs, hεs, hseed⟩ := Work.Diff.STE.B3.seed_half D ρ hρ hρ0 hρs hρ1 hg hJT
  set k₀ : ℕ := Module.finrank ℝ E + 13 with hk₀def
  have hk₀  : Module.finrank ℝ E + 12 < 2 * k₀ := by rw [hk₀def]; omega
  have hk₀4 : Module.finrank ℝ E + 4 ≤ k₀ := by rw [hk₀def]; omega
  have hk₀' : Module.finrank ℝ E + 4 < 2 * k₀ := by omega
  exact galUniform_of D hLC ρ hρ hρ0 hρs hρ1 hg hJN εs hεs hseed k₀ hk₀ hk₀4
    (D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) + 1) (le_refl _)
    (fun k hk4 => -- GardingSharpData at level k, from `gardingSharp` and `pdVec_defect_sharp k`)
    (fun k hk4 => -- TransportData at level k, from `GardDataL2_of_tame`)
    (fun k => -- CommData, from `Gal.galE_comm`)
    (fun k hk4 => GalTame.gardingSharp_hG_of_jet D hLC k k₀ hk4 hk₀' (…))
    (fun k hk4 => GalTame.lowEnergy_of_transport D hLC k k₀ (by omega) hk4 hk₀' (…))
    (GalTame.hapr_of_aPrioriL2 D hLC ρ hρ hρ0 hρs hρ1 hg k₀ hk₀ _ _ hJN (… k₀) (… k₀) (… k₀))
    (fun Cof hCof hap => GalTame.galerkin_trapped_strong D hLC ρ hρ hρ0 hρs hρ1 hg k₀ hk₀
        _ (le_refl _) (min εs 1) (lt_min hεs one_pos) hseed Cof hCof hap)
```

**The contracts** live in `GalTame/Contracts.lean` (`GardingSharpData`, `GardingData`,
`TransportData`, `LowEnergyData`, `CommData`, `DefectData`, `JNBound`, `CmptSmooth`) so that each
provider can be stated and proved without importing the modules still in flux.  Note that
`GardingSharpData`/`TransportData` still mention the order-1 chart-matrix jet `hjet`; the *wrappers*
`gardingSharp_hG_of_jet` and `lowEnergy_of_transport` (both proved) discharge it from the level-`k₀`
energy bound via `B3/BNorm_le_ENormB_unif` + `Lead/mat_jet_uniform_bound`.

**Proved and axiom-clean** (checked with `#print axioms`): `trapBounds`, `isGalSol_mono`,
`galUniform_of` (all in `lead/gal_uniform_assembly.lean`), `B3/BNorm_le_ENormB_unif`,
`B3/seed_margin`, `B3/dens_lower_bound`, `B3/R_contDiff_of_chartData`,
`Lead/mat_jet_uniform_bound`, `Lead/ENormB_le_BNorm_uniform`, `Lead/J_upper_bound`,
`GalTame/ENormB_mono_level`, `GalTame/galE_apriori_L2`, `GalTame/gardingSharp_hG_of_jet`,
`GalTame/lowEnergy_of_transport`, `GalTame/hapr_of_aPrioriL2`.

### ⚑ STATUS (current): the proof of `gal_uniform_v2` is COMPLETE and COMPILES

The proof in this file is written out in full (no `sorry` of its own): it instantiates
`Work.Diff.STE.Lead.galUniform_of` with

* `Work.Diff.STE.B3.seed_half` (proved, clean) for the seed margin with the constant `1/2`,
* `k₀ := Module.finrank ℝ E + 13`, `B := D.ENormB k₀ g₀.inner + D.ENormB 0 g₀.inner + 1`,
* `hGS` from `GalTame.gardingSharp` + `GalTame.pdVec_defect_sharp`,
* `hComm` from `Work.Diff.STE.Lead.Gal.galE_comm`,
* `hGk = gardingSharp_hG_of_jet ∘ hGS`, `hLowk = lowEnergyData_of` (`deTurck_low_energy` + the
  first-order-jet discharge),
* `hApr = hapr_of_aPrioriL2 …` (level `k₀`),
* `hTrap = galerkin_trapped_strong …` (with `ε₁ := min εs 1`).

`#print axioms Work.Diff.STE.Lead.gal_uniform_v2` currently reports `sorryAx`, and it comes **only**
from four providers (all in other agents' lanes):

1. `Work.Diff.STE.Lead.Gal.galE_comm` (`CommData`) — the order-`k` Friedrichs adjointness of
   `J ρ ε`; the last big analytic gap, being proved via `B3/SymCalc*`
   (flat Friedrichs gain + cross-chart transfer; a numerical check on the two-chart circle model
   confirms the ε-uniform bound).
2. `GalTame.pdVec_defect_sharp` (`DefectData`) — the sharp `L²` defect; the `hDefSharp` of
   `gardingSharp`.  (Axiom-tainted itself: 3 internal `sorry`s.)
3. `GalTame.gardingSharp` and `GalTame.deTurck_low_energy` — the sharp Gårding estimate and the
   low-energy bound of the DeTurck section.  Both are *proved* but their axiom closures still
   contain `sharpCoeff`, `sharpResid` (and `sharpTrans`, which uses them).

Everything else on the chain is proved **and axiom-clean** (verified with `#print axioms`):
`Lead/gal_uniform_assembly.lean` (`trapBounds`, `isGalSol_mono`, `galUniform_of`),
`B3/seed_half`, `B3/seed_margin`, `B3/BNorm_le_ENormB_unif`, `B3/dens_lower_bound`,
`B3/R_contDiff_of_chartData`, `Lead/mat_jet_uniform_bound`, `Lead/ENormB_le_BNorm_uniform`,
`Lead/J_upper_bound`, `GalTame/ENormB_mono_level`, `GalTame/galE_apriori_L2`,
`GalTame/gardingSharp_hG_of_jet`, `GalTame/lowEnergy_of_transport`, `GalTame/hapr_of_aPrioriL2`,
`GalTame/galerkin_trapped_solution`, `GalTame/galerkin_trapped_strong`.

So this file becomes `declare_proven`-able as soon as `galE_comm`, `pdVec_defect_sharp` and the
`sharpTrans`/`GN` chain are sorry-free — **no change to this file will be needed**.

The provider/contract shapes were verified at compile time
(`Submission/Work/Diff/STE/Lead/GalTame/_matchcheck.lean`): `DefectData k ⟹ GardingSharpData`,
`GardDataL2_of_tame ⟹ TransportData`, `galE_comm ⟹ CommData`,
`pdVec_defect_sharp k + (n + 4 ≤ k) ⟹ DefectData k`.

**Trap to remember**: `IsGalSol` gives `HasDerivWithinAt` of each *component* of
`s ↦ galState D ε (c s)`, which does *not* yield the coefficient-level
`HasDerivAt c (galVF2 … (c t)) t` without proving `galCoeff D ρ ε (genMap D ε a) = a`
(i.e. injectivity of `genMap`).  That is why the trapped solution must export the derivative
(hence `galerkin_trapped_strong`).

**Import-cycle rule of the subsystem**: no module under `Gal/` or `GalTame/` may import
`Lead/gal_uniform_v2` or `Lead/deTurck_limit`.  `Lead/gal_uniform_assembly.lean` no longer imports
*any* live target: it carries its own private copy of `ENormB ≤ C · BNorm`
(`enormb_le_bnorm_uniform_asm`, from `ENormSq_le_CSq_of_contDiff_periodic`) and uses
`GalTame/J_upper_bound_any` (clean) instead of `Lead/J_upper_bound`.  The target file itself
imports only `GalTame/*`, `Lead/gal_uniform_assembly` and `B3/seed_half`.

**`galE_comm`**: per the lead (13:14), `Lead/Gal/galE_comm.lean` is now an *alias* for
`B3/ENormB_pair_J_commutator_v2` (owner H2731), with identical statement and argument order
`(D ρ hρ hρ0 hρs hρ1 k hk hk1)`, so this file needs no edit when it lands.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

theorem gal_uniform_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hLC : LCSmooth I M) (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h))
    (hJT : (∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)), Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))) :
    GalUniform hLC D ρ := by
  classical
  -- 1. the seed margin, with the constant `1/2`
  obtain ⟨εs, hεs, hseed₀⟩ := Work.Diff.STE.B3.seed_half (I := I) (M := M) D ρ hρ hρ0
    hρs hρ1 hg hJT
  have hseed : ∀ (ε : ℝ), 0 < ε → ε ≤ εs → ∀ (x : M) (v : TangentSpace I x),
      (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v :=
    fun ε hε hε1 => hseed₀ ε ⟨hε, hε1⟩
  have hseed₁ : ∀ (ε : ℝ), 0 < ε → ε ≤ min εs 1 → ∀ (x : M) (v : TangentSpace I x),
      (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v :=
    fun ε hε hε1 => hseed ε hε (le_trans hε1 (min_le_left _ _))
  -- 2. the reference level `k₀` and the trapping level `B`
  set k₀ : ℕ := Module.finrank ℝ E + 13 with hk₀def
  have hk₀ : Module.finrank ℝ E + 12 < 2 * k₀ := by rw [hk₀def]; omega
  have hk₀4 : Module.finrank ℝ E + 4 ≤ k₀ := by rw [hk₀def]; omega
  have hk₀' : Module.finrank ℝ E + 4 < 2 * k₀ := by omega
  set B : ℝ := D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) + 1 with hBdef
  have hB : D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) + 1 ≤ B := le_of_eq hBdef.symm
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 : 0 ≤ D.ENormB k₀ (g₀.inner) :=
      Work.Diff.STE.Lead.GalTame.ENormB_nonneg_gal (I := I) (M := M) D k₀ _
    have h2 : 0 ≤ D.ENormB 0 (g₀.inner) :=
      Work.Diff.STE.Lead.GalTame.ENormB_nonneg_gal (I := I) (M := M) D 0 _
    linarith
  -- 3. the sharp defect, from `pdVec_defect_sharp`
  have hDef : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.DefectData (E := E) k := by
    intro k hk4
    obtain ⟨C, hC0, hCb⟩ :=
      Work.Diff.STE.Lead.GalTame.pdVec_defect_sharp (ι := Fin (Module.finrank ℝ E)) k
    refine ⟨C, hC0, ?_⟩
    intro A u KA S Q1 hA hAper hu hup hKA hS hQ1 h1 h2 h3 h4 h5 l
    exact hCb A u KA S Q1 hA hAper hu hup hKA hS hQ1 (by simpa using hk4) h1 h2 h3 h4 h5 l
  -- 4. the four providers
  have hGS : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.GardingSharpData (I := I) (M := M) D hLC k k₀ :=
    fun k hk4 => Work.Diff.STE.Lead.GalTame.gardingSharp (I := I) (M := M) D hLC k k₀ hk4 hk₀'
      (hDef k hk4)
  have hComm : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.CommData (I := I) (M := M) D ρ k :=
    fun k hk4 => Work.Diff.STE.Lead.Gal.galE_comm (I := I) (M := M) D ρ hρ hρ0 hρs hρ1 k
      (by omega) (by omega)
  have hGk : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.GardingData (I := I) (M := M) D hLC k k₀ :=
    fun k hk4 => Work.Diff.STE.Lead.GalTame.gardingSharp_hG_of_jet (I := I) (M := M) D hLC k k₀
      hk4 hk₀' (hGS k hk4)
  have hLowk : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.LowEnergyData (I := I) (M := M) D hLC k k₀ :=
    fun k hk4 => Work.Diff.STE.Lead.lowEnergyData_of (I := I) (M := M) D hLC k k₀
      (by omega) hk4 hk₀'
  -- 5. the assembly
  exact Work.Diff.STE.Lead.galUniform_of (I := I) (M := M) D hLC ρ hρ hρ0 hρs hρ1 hg hJN
    εs hεs hseed k₀ hk₀ hk₀4 B hB hGS hComm hGk hLowk
    (Work.Diff.STE.Lead.GalTame.hapr_of_aPrioriL2 (I := I) (M := M) D hLC ρ hρ hρ0 hρs hρ1 hg
      k₀ hk₀ B hB0 hJN (hComm k₀ hk₀4) (hGk k₀ hk₀4) (hLowk k₀ hk₀4))
    (fun Cof hCof hap => Work.Diff.STE.Lead.GalTame.galerkin_trapped_strong (I := I) (M := M)
      D hLC ρ hρ hρ0 hρs hρ1 hg k₀ hk₀ B hB (min εs 1) (lt_min hεs one_pos) hseed₁
      Cof hCof hap)

end

end Work.Diff.STE.Lead
