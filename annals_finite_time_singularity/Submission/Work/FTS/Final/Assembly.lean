import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.BSIdent.All
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.Final.Glue
import Submission.Work.FTS.Final.Small
import Submission.Work.FTS.MeridianDyn.All
import Submission.Work.FTS.Physical.BiotSavart.bsAdmissibleStripFull_comp_clock
import Submission.Work.FTS.RegPkgGal.Assembly
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le

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



end Work.FTS.Final
