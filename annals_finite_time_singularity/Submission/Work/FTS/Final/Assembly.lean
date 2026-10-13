/-
# `Work.FTS.Final.Assembly` — the end-to-end assembly (audit §4 item 11)

**Deliverable of the FTS/Final area:**

  `Work.FTS.Final.exists_blowupAt_of_inputs :
     (∃ α, Inputs α) → ∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1)`

## What the assembly *does*

From the input bundle `Inputs α` at some small exponent `α` (the bundle below), the proof

1. sets the profile exponent `α_G = pExp α = 3α`;
2. produces the **datum** `g₀ = locG6 α_G L β` from the *proved* `LocData6.locG6_data`
   (with the order-`6` class data `RegQ α_G 6`, `Xn α_G ≤ α_G²`, `Xn6 α_G ≤ K α_G²`);
3. invokes the **dynamic solution scheme** (conjunct 3, the `ε`-route) at that datum and then the
   **dynamic solution** (conjunct 4, the statement of `StrongEps.global_strong2`), obtaining `g`
   with `IsDynGSolWith (IsBslSolPos α_G) α_G (PsiCan Φs E g) g`, `RegPkgMin α_G g` and the uniform
   `ℋ⁴`-bound `Xn α_G (slice g τ) ≤ C₀ α_G²`;
4. builds the **clock** from the dynamic modulation `m s = muDyn α_G Φ g (max s 0)` by
   `Work.FTS.FinalClock.physClockOf`, with amplitude `C.A = 2·Avort m` and companion `B = Bdyn m`,
   and *verifies the clock data* `ClockData` (the modulation identity, the normalisation
   `C.A = 2A` — design correction 2, and the two ODEs) from `FinalClock.Avort_hasDerivAt` and
   `FinalClock.hasDerivAt_Bdyn_of_clock`;
5. invokes the analytic inputs (`RegPkg'`, `MeridianEqOn`, the Biot–Savart identification, the two
   differentiability clauses) and the pressure at the produced data;
6. concludes by `Work.FTS.Final.blowupAt_of_dyn_data`, i.e. `hsmall_of_H4` + the firing
   `FireFix.blowupAtTop_of_regPkg'` (`ω = −physOmega`, `pExp α`, `C.A = 2A`) + the rescale
   `Top.blowupAt_one_of_blowupAt` (node N0).

## The open inputs (all explicit, all in the bundle `Inputs α`)

| conjunct | owner | statement |
|---|---|---|
| `press` | `FTS/PressureOn` | `PressureReconstructionOn ⟨α, _⟩` |
| (1) | `FTS/EllSol` | the class-`C` linear operator: `EllPkgGo` and `EllPkgK 6` for `E g` |
| (2) | `FTS/PhiStar` | `StarPkgo2 α_G Cs Φs` |
| (3) | `FTS/StrongEps` | `EpsUniform α_G ρ Φs E g₀ C₀ K` at every admissible datum `g₀` |
| (4) | `FTS/StrongEps` | the statement of `global_strong2` (hypothesis `EpsUniform`) |
| (5) | `FTS/NonlinRows` | the pointwise sup bound `|g| ≤ Cg·Xn α_G (slice g τ)` |
| (6) | `CoercivityFix` | the modulation bound `|muDyn| ≤ 1/2` and its continuity |
| (7) | `FTS/RegPkgGal` | `∀ S > 0, RegPkg' α S A B g` from `RegPkgMin α_G g` (design item 10) |
| (8) | `FTS/MeridianDyn` | `MeridianEqOn` for the reconstruction |
| (9) | `FTS/BSIdent` | the identification of the velocity with the stream-function field |
| (10), (11) | `FTS/BSIdent` | the `C³` and `D²` clauses of the meridian pair |

The *proved* pieces are called, not assumed: the datum (`LocData6.locG6_data`), the clock
(`FinalClock.physClockOf`, `Avort_hasDerivAt`, `hasDerivAt_Bdyn_of_clock`), the Biot–Savart law
(`BSSwirl.biotSavartSwirl`), the firing (`FireFix.blowupAtTop_of_regPkg'`), the smallness
(`hsmall_of_H4`), the law additivity (`hPsi_of_pkgs`) and the rescale to `T = 1`
(`Top.blowupAt_one_of_blowupAt`).  `α · (600 Cg C₀) ≤ 1` is the smallness of `hsmall_of_H4`, carried
by the bundle because its `∃ α` lets the caller take `α` small.

A companion reduction is available in `FTS/Final/MeridianMin/`: the meridian conjunct (8) follows
from the `RegPkgMin` version of the bridge (`meridianEq_of_dynEq_of_regPkgMin`) applied to the
dynamics, whose remaining hypotheses are the `C²`-regularity of `Φ` on the quadrant, its oddness
in `θ` and the static derivation data `ProfDerivData`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.Final.Glue
import Submission.Work.FTS.Final.Psi
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS.RegPkgGal.Assembly
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.BSIdent.All
import Submission.Work.Elliptic.bslOp_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal
open MeasureTheory Set Filter

namespace Work.FTS.Final

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.FinalClock

set_option autoImplicit false

/-- **THE INPUT BUNDLE OF THE END-TO-END ASSEMBLY at the challenge exponent `α`.**

All the still-open inputs of the chain appear here, at the profile exponent `α_G := pExp α = 3α` and
in the shapes in which the assembly consumes them.  The fields are (see the module docstring for the
table of owners):

* `hα`, `hα13`, `press`;
* `core`: the single existential binding the elliptic operator `E`, the star profile `Φs`, the
  constants `Ce, Cs, Cg, C₀, K`, the mollifier `ρ` and the smallness `α(600 Cg C₀) ≤ 1`, together
  with the nine open analytic conjuncts.

The bundle is *satisfiable*: `α` may be taken arbitrarily small; the datum comes from
`LocData6.locG6_data`, the clock from `FinalClock`, the Biot–Savart law from `BSSwirl`, and the
fire/rescale from `FireFix`/`Top`. -/
structure Inputs (α : ℝ) : Prop where
  /-- the challenge exponent is positive -/
  hα : 0 < α
  /-- and lies in the paper's regime -/
  hα13 : α ≤ 1 / 3
  /-- the pressure reconstruction at this exponent -/
  press : PressureReconstructionOn ⟨α, hα.le⟩
  /-- **the existential core** -/
  core : ∃ (Ce Cs Cg C₀ K : ℝ) (ρ : ℝ × ℝ → ℝ) (E : Fn →ₗ[ℝ] Fn) (Φs : Fn),
    0 < Ce ∧ 0 ≤ Cg ∧ 0 < C₀ ∧ 0 < K ∧ α * (600 * Cg * C₀) ≤ 1 ∧
    -- (0) the mollifier kernel of the scheme (ruling v2, D3)
    Work.FTS.StrongEps.IsSmoothKernel ρ ∧
    -- (1) the elliptic layer on the class C, at the profile exponent (owner: EllSol; this is
    -- `ClassC.ExistsEllSolC` at `pExp α`, see `core1_of_existsEllSolC`)
    (∀ g : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) g →
      EllPkgGo (Work.FTS.Regularity.pExp α) Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce g (E g)) ∧
    -- (1a) `E` passes to limits of bounded class-C sequences (owner: EllSol, A6)
    Work.FTS.StrongEps.EllLimOK (Work.FTS.Regularity.pExp α) E ∧
    -- (1b) the modulation bounds on class C (owner: CoercivityFix)
    Work.FTS.StrongEps.MuLamOK (Work.FTS.Regularity.pExp α) C₀ Φs E ∧
    -- (2) the star package, at the profile exponent (owner: PhiStar)
    StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs ∧
    -- (3) E4: the epsilon-scheme at every regular admissible datum (owner: StrongEps)
    (∀ (K' : ℝ) (g₀ : Fn), Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6 g₀ →
      (∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε g₀) →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) g₀ ≤ (Work.FTS.Regularity.pExp α) ^ 2 →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) g₀
          ≤ K' * (Work.FTS.Regularity.pExp α) ^ 2 →
      Work.FTS.StrongEps.EpsUniformMem (Work.FTS.Regularity.pExp α) ρ Φs E g₀ C₀ K') ∧
    -- (3a′) the localized data with the normalising `β` (`L₁₂(locG6)(0) = 0`, as chosen by
    -- `LocData6.locG6_data`) are regular data of the scheme (owner: FTS_LocDatum3a)
    (∀ L β : ℝ, 1 ≤ L → Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) →
      Work.Construction.L12 (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) 0 = 0 →
      ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β)) ∧
    -- (4) the dynamic solution at the core's own `ρ Φs E` (owner: StrongEps; `global_strong2`
    -- applied with (0), (1), (1a), (2), (1b) and `pExp α ≤ α₂`)
    (∀ (g₀ : Fn) (K' : ℝ),
      Work.FTS.StrongEps.EpsUniformMem (Work.FTS.Regularity.pExp α) ρ Φs E g₀ C₀ K' →
      ∃ gg : Fam,
        IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
          (PsiCan Φs E gg) gg ∧
        DynOK (Work.FTS.Regularity.pExp α) C₀ gg) ∧
    -- (5) the pointwise sup bound (owner: NonlinRows)
    (∀ g : Fam, DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |g z θ τ| ≤ Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ)) ∧
    -- (6) the modulation data of the clock (owner: CoercivityFix)
    (∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
          (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g)
        (Set.Ici 0)) ∧
    -- (7) the corrected regularity package (owner: RegPkgGal, design item 10); the ten `A`/`B`-
    -- clauses of `RegPkg'` must be a *hypothesis* (they are false for an arbitrary pair `A B`)
    (∀ (g : Fam) (A B : ℝ → ℝ),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      (∀ S : ℝ, 0 < S → ClockPkg α S A B) →
      ∀ S : ℝ, 0 < S → RegPkg' α S A B g) ∧
    -- (8) the meridian equation (owner: MeridianDyn)
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
        (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B (PsiCan Φs E g) C) C.T) ∧
    -- (9) the Biot-Savart identification (owner: BSIdent); the clock data gives `0 < B`
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B
                (PsiCan Φs E g) C r z t) x) ∧
    -- (10) the C^3-clause of the meridian pair (owner: BSIdent); the `C^3`-regularity of the
    -- stream function on the quadrant is an explicit hypothesis (it is a fact about `Phi`, not
    -- about the clock)
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      (∀ τ : ℝ, 0 < τ → ContDiffOn ℝ 3
        (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
        ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
          Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B (PsiCan Φs E g) C
            p.1 p.2 t) (r, z)) ∧
    -- (11) the D^2-clause of the meridian pair (owner: BSIdent); the clock data is needed, since
    -- the profile's first argument `ρ^{3α}/B(σ)` must be positive (it is not for an arbitrary `B`)
    (∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
        Work.Cyl.DiffAt2 (fun r z => Work.FTS.Physical.merProfile α A B g C r z t) r z) ∧
    -- (12) the ten clock clauses of `RegPkg'` at the clock amplitudes of the dynamic modulation
    -- (owner: RegPkgGal / the modulation estimates `hm`, `hmb`, `hmh` of `GalHyp`; design §2)
    (∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ S : ℝ, 0 < S →
        ClockPkg α S (ampA (maxMu (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g))
          (ampB (maxMu (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g))) ∧
    -- (13) the stream function of the reconstruction is `C^3` on the open quadrant (owner: the
    -- elliptic layer — it is `PhiTil`-smoothness of `PsiCan Phi_s E g`; consumed by `(10)`)
    (∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ τ : ℝ, 0 < τ →
        ContDiffOn ℝ 3 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)

/-- **THE END-TO-END ASSEMBLY (audit §4 items 1, 2 and 11), with every open input as an
explicit hypothesis.**

From the challenge exponent `α ∈ (0, 1/3]` and the still-open inputs of the chain — *verbatim*
copies of the statements of their owners' files — a finite-time blow-up at time `1` of the
incompressible Euler equations on `ℝ³` in node N0's interface:

  `∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1)`.

The hypotheses are, in order:

* `hEll`, `hStar` — the elliptic layer on the class `C` (`FTS/EllSol`) and the star package
  (`FTS/PhiStar`), at the profile exponent `pExp α = 3α`;
* `hEps`, `hDyn` — the `ε`-scheme (`EpsUniform` at every admissible datum: the three datum
  hypotheses are exactly those produced by the proved `LocData6.locG6_data`) and the dynamic
  solution (`StrongEps.global_strong2`'s statement);
* `hSup` — the pointwise sup bound (`FTS/NonlinRows`);
* `hMu` — the modulation bound and continuity (`CoercivityFix`);
* `hReg` — the corrected regularity package (`FTS/RegPkgGal`, design item 10);
* `hMer` — the meridian equation (`FTS/MeridianDyn`);
* `hHid`, `hPsi`, `hW` — the Biot–Savart identification and the two differentiability clauses
  (`FTS/BSIdent`);
* `hpress` — the pressure reconstruction (`FTS/PressureOn`).

The *proved* pieces are invoked, not assumed: `LocData6.locG6_data` (the datum),
`FinalClock.physClockOf` + `Avort_hasDerivAt` + `hasDerivAt_Bdyn_of_clock` (the clock and its
data, design corrections 1–2), `BSSwirl.biotSavartSwirl`, `FireFix.blowupAtTop_of_regPkg'`,
`hsmall_of_H4` and `Top.blowupAt_one_of_blowupAt`. -/
theorem exists_blowupAt_of_data {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Ce Cs Cg C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {E : Fn →ₗ[ℝ] Fn} {Φs : Fn}
    (hCg : 0 ≤ Cg) (hC₀ : 0 < C₀) (hK : 0 < K) (hscale : α * (600 * Cg * C₀) ≤ 1)
    (_hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (_hEll : ∀ g : Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) g →
      EllPkgGo (Work.FTS.Regularity.pExp α) Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce g (E g))
    (_hEL : Work.FTS.StrongEps.EllLimOK (Work.FTS.Regularity.pExp α) E)
    (_hML : Work.FTS.StrongEps.MuLamOK (Work.FTS.Regularity.pExp α) C₀ Φs E)
    (_hStar : StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hEps : ∀ (K' : ℝ) (g₀ : Fn), Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6 g₀ →
      (∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε g₀) →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) g₀ ≤ (Work.FTS.Regularity.pExp α) ^ 2 →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) g₀
          ≤ K' * (Work.FTS.Regularity.pExp α) ^ 2 →
      Work.FTS.StrongEps.EpsUniformMem (Work.FTS.Regularity.pExp α) ρ Φs E g₀ C₀ K')
    (hDat : ∀ L β : ℝ, 1 ≤ L → Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 6
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) →
      Work.Construction.L12 (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) 0 = 0 →
      ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum (Work.FTS.Regularity.pExp α) ρ ε
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β))
    (hDyn : ∀ (g₀ : Fn) (K' : ℝ),
      Work.FTS.StrongEps.EpsUniformMem (Work.FTS.Regularity.pExp α) ρ Φs E g₀ C₀ K' →
      ∃ gg : Fam,
        IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
          (PsiCan Φs E gg) gg ∧
        DynOK (Work.FTS.Regularity.pExp α) C₀ gg)
    (hSup : ∀ g : Fam, DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |g z θ τ| ≤ Cg * Xn (Work.FTS.Regularity.pExp α) (slice g τ))
    (hMu : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
          (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g)
        (Set.Ici 0))
    (hReg : ∀ (g : Fam) (A B : ℝ → ℝ),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      (∀ S : ℝ, 0 < S → ClockPkg α S A B) →
      ∀ S : ℝ, 0 < S → RegPkg' α S A B g)
    (hMer : ∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
        (Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B (PsiCan Φs E g) C) C.T)
    (hHid : ∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B
                (PsiCan Φs E g) C r z t) x)
    (hPsi : ∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      (∀ τ : ℝ, 0 < τ → ContDiffOn ℝ 3
        (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
        ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
          Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B (PsiCan Φs E g) C
            p.1 p.2 t) (r, z))
    (hW : ∀ (g : Fam) (A B : ℝ → ℝ) (C : PhysClock),
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
        Work.Cyl.DiffAt2 (fun r z => Work.FTS.Physical.merProfile α A B g C r z t) r z)
    (hClockPkg : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ S : ℝ, 0 < S →
        ClockPkg α S (ampA (maxMu (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g))
          (ampB (maxMu (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g)))
    (hPhiSm : ∀ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs E g) g → DynOK (Work.FTS.Regularity.pExp α) C₀ g →
      ∀ τ : ℝ, 0 < τ →
        ContDiffOn ℝ 3 (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hpress : PressureReconstructionOn ⟨α, hα.le⟩) :
    ∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1) := by
  -- the profile exponent
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the datum, from the *proved* `LocData6.locG6_data`
  obtain ⟨L₀, _hL₀, hL⟩ := Work.FTS.LocData6.locG6_data (Work.FTS.Regularity.pExp α) hαG hαG1 K hK
  obtain ⟨β, _hβ, _hAdm, hRegQ, _hGal, hL12, hXn4₀, hXn6₀⟩ := hL (max L₀ 1) (le_max_left _ _)
  -- the dynamic solution at that datum
  have hU : Work.FTS.StrongEps.EpsUniformMem (Work.FTS.Regularity.pExp α) ρ Φs E
      (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) (max L₀ 1) β) C₀ K :=
    hEps K (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) (max L₀ 1) β)
      hRegQ (hDat (max L₀ 1) β (le_max_right _ _) hRegQ hL12) hXn4₀ hXn6₀
  obtain ⟨g, hSol, hDynOK⟩ := hDyn
    (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) (max L₀ 1) β) K hU
  -- the clock (design item 8; `FinalClock.physClockOf` is the clock of `physClock_of_dyn`)
  obtain ⟨hμ, hc⟩ := hMu g hSol hDynOK
  set m : ℝ → ℝ := maxMu (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g with hm
  have hcm : Continuous m := continuous_maxExt hc
  have hmb : MuBound m := maxExt_bound hμ
  set C : PhysClock := physClockOf m hcm hmb with hC
  set A : ℝ → ℝ := ampA m with hA
  set B : ℝ → ℝ := ampB m with hB
  have hCmuA : C.mu = m := rfl
  -- the clock data (design correction 2: `C.A = 2A`)
  have hClock : ClockData (Work.FTS.Regularity.pExp α) (PsiCan Φs E g) g A B C := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hCmuA, hm, maxMu, max_eq_left hτ]
    · intro τ hτ
      rw [hA]
      rfl
    · intro τ hτ
      rw [hA, hCmuA]
      simpa only [ampA] using Avort_hasDerivAt hcm τ
    · intro τ hτ
      rw [hB, hCmuA]
      have h := hasDerivAt_Bdyn_of_clock m hcm hmb 1 τ
      rw [physClockOf_mu] at h
      simpa only [ampB, one_mul] using h
    · intro τ hτ
      rw [hB]
      simpa only [ampB] using Bdyn_pos m τ
  have hClockPkgA : ∀ S : ℝ, 0 < S → ClockPkg α S A B := by
    intro S hS
    simpa only [hA, hB] using hClockPkg g hSol hDynOK S hS
  have hPhiC : ∀ τ : ℝ, 0 < τ → ContDiffOn ℝ 3
      (fun q : ℝ × ℝ => PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd :=
    fun τ hτ => hPhiSm g hSol hDynOK τ hτ
  exact ⟨⟨α, hα.le⟩, hα, blowupAt_of_dyn_data hα hα13 hCg hC₀ hscale
    (fun τ hτ => hDynOK.2 τ hτ) (fun τ hτ => hSup g hDynOK τ hτ) hClock.2.1
    (hReg g A B hSol hDynOK hClockPkgA) (hMer g A B C hSol hDynOK hClock)
    (hHid g A B C hSol hDynOK hClock) (hPsi g A B C hSol hDynOK hClock hPhiC)
    (hW g A B C hSol hDynOK hClock) hpress⟩

/-- **THE END-TO-END ASSEMBLY, packaged.**  Same conclusion as `exists_blowupAt_of_data`, from the
input bundle `Inputs α` at *some* small exponent `α`.  This is the shape in which the final wiring
of `Submission.lean` consumes the area:

```lean
obtain ⟨α, hα, ⟨B⟩⟩ := Work.FTS.Final.exists_blowupAt_of_inputs h
exact Work.FTS.Top.theorem_1_of_blowupAt hα B
``` -/
theorem exists_blowupAt_of_inputs (h : ∃ α : ℝ, Inputs α) :
    ∃ α : ℝ≥0, 0 < (α : ℝ) ∧ Nonempty (Work.FTS.Top.BlowupAt α 1) := by
  obtain ⟨α, hα, hα13, hpress, core⟩ := h
  obtain ⟨Ce, Cs, Cg, C₀, K, ρ, E, Φs, _hCe, hCg, hC₀, hK, hscale, hρ, hEll, hEL, hML, hStar,
    hEps, hDat, hDyn, hSup, hMu, hReg, hMer, hHid, hPsi, hW, hClockPkg, hPhiSm⟩ := core
  exact exists_blowupAt_of_data hα hα13 hCg hC₀ hK hscale hρ hEll hEL hML hStar hEps hDat hDyn
    hSup hMu hReg hMer hHid hPsi hW hClockPkg hPhiSm hpress

end Work.FTS.Final
