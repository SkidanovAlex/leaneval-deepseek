/-
# `Work.ConstructionInstance.Patch` — the signed patch of the delivered interface

`Submission/Work/SolutionDelivery/Scaling/Patch.lean` established the house style for a finding of
this kind: ship the *repaired* statement, its proof, the drop-in consumers, and certificates in the
shape of the patched call.  This file does that for the defects that this directory proves in the
delivered interfaces.

## The findings

* **(A) the datum clause.**  `ConstructedSolution.ωS_cdh : IsContDiffHolder ℝ α ωS` is **false**
  for the honest self-similar vorticity: for every profile exponent `p < 1` the field `omegaS p g`
  is not differentiable at the origin (`Refute.not_differentiableAt_omegaS_of_quad`).  The true
  hypothesis `Holder α ωS` (plus boundedness) is all the assembly consumes
  (`holder_omegaS_of_data`); `Repair.lean` certifies the patch at the three call sites.
* **(B) the `L^∞` boxes.**  `hBdd`/`hBddDt` bound `ω`/`∂ₜω` *uniformly in `t`*; with `hansatz` and
  `hlam_le` this is **contradictory** (`Obstruction.not_nonempty_constructedSolution`).  The true
  box is `λ̄(t)·‖ω(x,t)‖ ≤ M` (`Boxes.lam_mul_norm_le_of_ansatz`), resp. `λ̄(t)²·‖∂ₜω‖ ≤ M₁`;
  the same clash sits in `Work.StabilityFar.AssemblyInputs`
  (`not_slicesBounded_of_vortLinfLower`), whose repair is the *strip* form
  (`strip_bdd_of_repaired`).
* **(C) the window of the `λ̄`-fields.**  `λ̄ > 0` *and* differentiable at `T` together with
  `λ̄(t) ≤ 2(T-t)` on `[0,T)` is empty (`not_lam_pos_extWindow`); every `λ̄`- and box-field below
  lives on `preWindow T = Ioo (-2) T`.
* **(D) the smoothness class of `Linf_H2`.**  `Work.Spaces.Linf_H2` assumes the *analytic* class
  `SmoothNbhd`, while the construction's `St1` class is `SmoothFar` (C^∞); the field `hCgbig` is
  stated with the class the delivered lemma consumes.
* **(E) the time-Hölder constant.**  A uniform-in-`t` constant `H` on a window that straddles `T`
  cannot coexist with `St5`: with `hansatz`, `hSupp` and the bound at `t = 0` it gives
  `c₀α ≤ λ̄(t)(M/λ̄(0) + H t^α) ≤ 2(T-t)(…) → 0` (`not_timeHolderOnBall_window`).  The honest field
  is the **strip** form `∀S, 0 < S → S+1 < T → ∃H, TimeHolderOnBall α ω R S H`
  (`solVort_timeHolder`).
* **(F) the ansatz must carry the cut-off.**  `SlicesSupported ω R T` needs a compactly supported
  slice; the *uncut* field `omegaS p g` vanishes only at the axis and the plane (`g = 0`: nowhere
  else on the open quadrant), so no `R` works.  The constructed vorticity is therefore the **cut**
  field `SelfSim.selfSimVort`, whose support is `B(0,2L)` for every `t`, independently of the flow.

## The reconciliation: what is left, and where it comes from

After (A)–(F) and the derivations in `Reduced.lean`, the residual interface of this directory is

```lean
structure ConstructionDataFixed (α : NNReal) where
  lwp : Work.LWP.LWPInputs α                      -- the LWP chapter's analytic input bundle
  prof : ProfileData α                            -- profile + modulation + the two parameters
  hmax : Work.LWP.MaximalSolution α … prof.T      -- the chapter's maximal solution
  smooth : ContDiffOn ℝ 1 hmax.u.uncurry …        -- the backward extension of the solution
  bsSliceExt : hmax.u x t = BS (solVort prof · t) x
```

* `ProfileData α` is **inhabited** (`profileData_inhabited`): the perturbation `g = 0`, `T = 2`,
  `λ̄(t) = 1 - t/2`, `K = 1/2`, `L = 4^{1/p}+1`, `R = 2L`, `M = 20p`, `M₁ = 10p`
  (with `T = 2` the strip condition `S + 1 < T`, `S > 0` of the strip-indexed fields is
  satisfiable, so the inhabitant does not trivialise them).
* the other three fields (`hmax`, `smooth`, `bsSliceExt` — plus the bundle `lwp`) say exactly that
  the maximal solution of `Work.LWP` for the cut-off self-similar datum **is** the self-similar
  solution; that is the content of the `St0`–`St3` bootstrap of `Work.Stability` and of the
  backward extension, and nothing inside this directory can produce it.
* the `ωS`-side of the delivered package (`ωS`, `ωS_meas`, `ωS_holder`, `ωS_bdd`, `ωS_div`,
  `ωS_odd`, `L`) is derived from `ProfileData`, and the whole solution side (`ω`, `hSupp`, `hDivω`,
  `hωcont`, `hBdd`, `hBddDt`, `hTh`, `hansatz`, `lam`, `c₀`) is derived by `Reduced.lean`.

## The call the lead pastes (after the patch)

```lean
exact Work.SolutionDelivery.theorem_1_of_constructed
  (Work.ConstructionInstance.constructedSolutionFixed D) hα hα1
```

with `D : Work.ConstructionInstance.ConstructionDataFixed α`; the certificates at the end of this
file are the literal patched call shapes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.ModulatedData
import Submission.Work.ConstructionInstance.Repair
import Submission.Work.ConstructionInstance.Data
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The repaired input package -/

/-- **The repaired constructed-solution package**: `Work.SolutionDelivery.ConstructedSolution`
with the defects (A)–(F) patched — the datum clause is the true `Holder α ωS`, the two `L^∞` boxes
carry the self-similar weights `λ̄(t)` resp. `λ̄(t)²`, every window field lives on
`preWindow T = Ioo (-2) T`, and the time-Hölder field is the strip form of finding (E). -/
structure ConstructedSolutionFixed (α : NNReal) where
  /-- the analytic inputs of the LWP/continuation chapter -/
  lwp : Work.LWP.LWPInputs α
  /-- the support radius of the vorticity -/
  R : ℝ
  /-- `R > 0` -/
  hR : 0 < R
  /-- the self-similar `L^∞` constant -/
  M : ℝ
  /-- `M ≥ 0` -/
  hM : 0 ≤ M
  /-- the self-similar `L^∞` constant of `∂ₜω` -/
  M₁ : ℝ
  /-- `M₁ ≥ 0` -/
  hM₁ : 0 ≤ M₁
  /-- the `St1` cut-off parameter -/
  L : ℝ
  /-- `L > 0` -/
  hL : 0 < L
  /-- the paper's self-similar initial vorticity (before the cut-off) -/
  ωS : R3 → R3
  /-- `ωS` is measurable -/
  ωS_meas : MeasureTheory.AEStronglyMeasurable ωS MeasureTheory.volume
  /-- **the repaired datum clause**: `ωS` is `α`-Hölder -/
  ωS_holder : Holder α ωS
  /-- `ωS` is bounded by `M` -/
  ωS_bdd : ∀ x : R3, ‖ωS x‖ ≤ M
  /-- the cut-off datum is divergence-free (the `Cyl` dictionary) -/
  ωS_div : ∀ x : R3, FiniteTimeSingularity.div (Work.SolutionDelivery.cutDatum L ωS) x = 0
  /-- the Biot–Savart field of the cut-off datum is odd (the `Cyl` parity dictionary) -/
  ωS_odd : FiniteTimeSingularity.IsOdd
    (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS))
  /-- the maximal time of the constructed solution -/
  T : ℝ
  /-- the LWP chapter's maximal solution with datum `u₀ = BS ω₀` -/
  hmax : Work.LWP.MaximalSolution α
    (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum L ωS)) T
  /-- `u.uncurry` is `C¹` near the half-window -/
  smooth : ContDiffOn ℝ 1 hmax.u.uncurry (Set.univ ×ˢ preWindow T)
  /-- the vorticity of the constructed solution -/
  ω : R3 → ℝ → R3
  /-- `u(x,t) = BS(ω(·,t)) x` on the half-window -/
  bsSliceExt : ∀ t ∈ preWindow T, ∀ x : R3,
    hmax.u x t = Work.LWP.biotSavart (fun y => ω y t) x
  /-- the vorticity slices are supported in `B(0,R)` -/
  hSupp : ∀ t ∈ preWindow T, ∀ y : R3, ω y t ≠ 0 → y ∈ Metric.closedBall 0 R
  /-- the vorticity slices are divergence-free -/
  hDivω : ∀ t ∈ preWindow T, FiniteTimeSingularity.div (ω · t) = 0
  /-- **the core regularity of the vorticity, in its honest shape**: continuity, not `C¹` -/
  hωcont : ContinuousOn (Function.uncurry ω)
    (Work.StabilityFar.coreRegion (R + 1) ×ˢ preWindow T)
  /-- the modulation `λ̄` -/
  lam : ℝ → ℝ
  /-- `λ̄ > 0` on `[0,T)` -/
  hlam_pos : ∀ t ∈ Set.Ico 0 T, 0 < lam t
  /-- `λ̄(t) ≤ 2(T-t)` on `[0,T)` -/
  hlam_le : ∀ t ∈ Set.Ico 0 T, lam t ≤ 2 * (T - t)
  /-- `(T-t)/2 ≤ λ̄(t)` on `[0,T)` -/
  hlam_low : ∀ t ∈ Set.Ico 0 T, (T - t) / 2 ≤ lam t
  /-- **the repaired box**: the `L^∞` bound is uniform in the *self-similar* variable -/
  hBdd : ∀ t ∈ preWindow T, ∀ y : R3, lam t * ‖ω y t‖ ≤ M
  /-- the same for `∂ₜω`, with the honest `λ̄²` weight -/
  hBddDt : ∀ t ∈ preWindow T, ∀ y : R3,
    (lam t) ^ 2 * ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁
  /-- **the time-Hölder field, in its strip form** (finding E) -/
  hTh : ∀ S : ℝ, 0 < S → S + 1 < T → ∃ H : ℝ, 0 ≤ H ∧
    Work.StabilityFar.TimeHolderOnBall (α : ℝ) ω R S H
  /-- **the time-Hölder field of `∂ₜω`, in its strip form** (finding H).  The far-field step
  `Work.StabilityFar.st4_farField_holder_of_vorticity` consumes the time-Hölder regularity of
  *both* `ω` and `∂ₜω`; in the delivered interface both are consequences of the single field
  `hωcore : IsContDiffHolderOn ℝ α ω.uncurry …` (via
  `Work.SolutionDelivery.Holder`), but that field is false for the honest vorticity (finding A),
  so the repaired interface must carry the two strip forms separately.  This one is *not*
  derivable from the others: it is control of `∂ₜ²ω` (see
  `Work.ConstructionInstance.timeHolderOnBall_timeDeriv_of_secondDeriv`). -/
  hThDt : ∀ S : ℝ, 0 < S → S + 1 < T → ∃ H₁ : ℝ, 0 ≤ H₁ ∧
    Work.StabilityFar.TimeHolderOnBall (α : ℝ) (FiniteTimeSingularity.timeDeriv ω) R S H₁
  /-- the `St5` constant -/
  c₀ : ℝ
  /-- `c₀ > 0` -/
  hc₀ : 0 < c₀
  /-- **the `St5` interface** -/
  hansatz : ∀ t ∈ Set.Ico 0 T, ∃ x : R3, c₀ * (α : ℝ) ≤ lam t * ‖ω x t‖

/-- **The named residual of the construction** (the single hypothesis that this directory cannot
discharge): *the chapter's maximal Euler solution for the cut-off self-similar datum is the
self-similar one*.  It bundles the three fields the delivered interface needs about the solution
side — the maximal solution at time `T`, the Biot–Savart tie `u(·,t) = BS(ω(·,t))`, and the `C¹`
regularity of the velocity near the half-window.

The components of this statement, and where each comes from, are recorded in `NOTES.md` §3.3:

* the velocity/vorticity identification `u = BS(ω(·,t))` is *by construction* of the candidate `u`,
  and the datum matches at `t = 0` by the normalisation `λ̄(0) = 1` (finding G,
  `solVort_zero_eq_cutDatum`);
* every slice property is a **theorem** of this directory (`solVort_integrable`,
  `solVort_isBoundedFun`, `solVort_holder`, `solVort_div`, `vorticity_biotSavart_solVort`,
  `isOdd_biotSavart_solVort`, `solVort_timeHolder_Icc`);
* what remains is two analytic outputs of the sibling chapters: the **Euler vorticity equation**
  `∂ₜω + (u·∇)ω = (ω·∇)u` for the constructed field (the `St0`–`St3` bootstrap of
  `Work.Stability`, whose profile-level form is `DynEq`/`SelfSimEulerS`) and the **spacetime
  Lichtenstein–Gunther class** of `BS(ω(·,t))` (the `LWP` inputs give the Schauder estimate *per
  slice*, `BiotSavartSchauder α`, which is non-quantitative and cannot be upgraded to joint
  `(x,t)` regularity);
* the maximality of `T` follows from `St5` (`‖ω(·,t)‖_∞ ≳ 1/λ̄(t)`) and the Beale–Kato–Majda
  criterion (`lwp.bkm`), once the above is in place. -/
def SelfSimilarEulerSolution (α : NNReal) (T : ℝ) (P : ProfileData α) : Prop :=
  ∃ hm : Work.LWP.MaximalSolution α
      (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) T,
    (∀ t ∈ preWindow T, ∀ x : R3,
      hm.u x t = Work.LWP.biotSavart (fun y => solVort P y t) x) ∧
    ContDiffOn ℝ 1 hm.u.uncurry (Set.univ ×ˢ preWindow T)

/-- **`tie` component 1, named in the chapters' vocabulary**: the constructed vorticity solves the
Euler **vorticity equation** against `u = BS ω`.  This is the `St0`–`St3` output of
`Work.Stability`, whose profile-level form is `Work.Stability.DynEq` / `SelfSimEulerS`
(`Work.Stability.DynEqOfSelfSimEulerS` relates the two), together with the bootstrap it is proved
from (`Work.Stability.GEquationWithFar`, `St3Inputs`, `FarControl`). -/
def SelfSimVorticityEquation (α : NNReal) (P : ProfileData α) : Prop :=
  Work.LWP.VorticityEquation
    (fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x) (solVort P)

/-- **`tie` component 2, named in the chapters' vocabulary**: the reconstructed velocity
`x ↦ BS(ω(x,t))` is in the **spacetime Lichtenstein–Gunther class** on every strip `[0,S]`,
`S < T`.  This is the `LWP` chapter's `LGClass` regularity; note that the per-slice Schauder input
(`Work.LWP.BiotSavartSchauder`) is *not* enough for it. -/
def SelfSimLGClass (α : NNReal) (P : ProfileData α) : Prop :=
  ∀ S ∈ Set.Ioo (0 : ℝ) P.T,
    IsContDiffHolderOn ℝ α
      (fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => solVort P y q.2) q.1)
      (Set.univ ×ˢ Set.Icc 0 S)

/-- **The residual of finding (H): the time-Hölder regularity of `∂ₜω` on the strips.**

`Work.StabilityFar.st4_farField_holder_of_vorticity` needs `TimeHolderOnBall α (∂ₜω) R S H₁` for
every strip `S` with `S + 1 < T` — the time-regularity of the *time derivative* of the vorticity,
i.e. control of `∂ₜ²ω` (see `timeHolderOnBall_timeDeriv_of_secondDeriv`).  For the honest
self-similar field it holds (the ansatz is `C^∞` in `t` on every strip), but it is *not* implied
by the other fields of the interface. -/
def SelfSimTimeHolderDeriv {α : NNReal} (P : ProfileData α) : Prop :=
  ∀ S : ℝ, 0 < S → S + 1 < P.T → ∃ H₁ : ℝ, 0 ≤ H₁ ∧
    Work.StabilityFar.TimeHolderOnBall (α : ℝ)
      (FiniteTimeSingularity.timeDeriv (solVort P)) P.R S H₁

/-- **The residual interface of this directory**: the LWP chapter's analytic input bundle, the
profile/modulation data (inhabited: `profileData_inhabited`), and the one named statement that the
construction is about. -/
structure ConstructionDataFixed (α : NNReal) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- the profile, the modulation and the two geometric parameters -/
  prof : ProfileData α
  /-- **the named residual `tie`**: the chapter's maximal solution is the self-similar one -/
  tie : SelfSimilarEulerSolution α prof.T prof
  /-- **the named residual of finding (H)**: the time-Hölder regularity of `∂ₜω` on the strips.
  Equivalently (see `timeHolderOnBall_timeDeriv_of_secondDeriv`) a bound on `∂ₜ²ω`; see
  `NOTES.md` §3.5 for the roadmap. -/
  hThDt : SelfSimTimeHolderDeriv prof

/-- **The instantiation into the repaired package.**  Everything is derived: the datum side
(`ωS := omegaS (profExp α) D.prof.g` with its measurability, Hölder regularity, `L^∞` bound,
divergence-freeness and parity) and the whole solution side (`solVort D.prof` with its support,
boxes, divergence-freeness, continuity, strip time-Hölder bound and `St5`). -/
def constructedSolutionFixed {α : NNReal} (D : ConstructionDataFixed α) :
    ConstructedSolutionFixed α :=
  let P := D.prof
  let hp : 0 < profExp α := profExp_pos P.hα
  let hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  { lwp := D.lwp
    R := P.R
    hR := lt_of_lt_of_le (by linarith [P.hL]) P.hRbig
    M := P.M
    hM := P.hM
    M₁ := P.M₁
    hM₁ := P.hM₁
    L := P.L
    hL := P.hL
    ωS := omegaS (profExp α) P.g
    ωS_meas := aestronglyMeasurable_omegaS P.hmeasP
    ωS_holder := holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ P.hvt P.hquad0 P.hquad
      P.hvan P.hzk P.hzth (P.hsmooth.of_le le_top)
    ωS_bdd := fun x => omegaS_norm_le hp hp1 (bdd_g P) P.hCg (fun θ hθ => by
      have hG : Gamma (profExp α / 3) θ ≤ 1 :=
        Gamma_le_one (by rw [profExp]; positivity) hθ
      have hG0 : 0 ≤ Gamma (profExp α / 3) θ := Gamma_nonneg hθ
      have hp0 : 0 ≤ profExp α := profExp_nonneg α
      nlinarith [P.hMprof, hG, hG0, hp0]) x
    ωS_div := div_omega0_all hp hp1 P.hvt (Work.Stability.SmoothFar.of_smoothNbhd P.hsmooth) P.L
    ωS_odd := Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl
      (isOddVorticity_cutDatum (isOddVorticity_omegaS (by rw [profExp]; positivity) P.hvt))
      (isAxiNoSwirl_omega₀ _ _ _)
    T := P.T
    hmax := D.tie.choose
    smooth := D.tie.choose_spec.2
    ω := solVort P
    bsSliceExt := D.tie.choose_spec.1
    hSupp := fun t _ y hy => solVort_supp P t y hy
    hDivω := fun t ht => solVort_div P t ht
    hωcont := solVort_cont P
    lam := P.lam
    hlam_pos := fun t ht => P.hlam t ⟨by linarith [ht.1], ht.2⟩
    hlam_le := P.hlam_le
    hlam_low := P.hlam_low
    hBdd := solVort_bdd P
    hBddDt := solVort_bddDt P
    hTh := fun S hS hST => solVort_timeHolder P S hS hST
    hThDt := D.hThDt
    c₀ := c₀star α
    hc₀ := c₀star_pos P.hα P.hα13
    hansatz := solVort_hansatz P }

/-! ## The strip consequence of the repaired box -/

/-- **The repaired box yields the honest *strip* bound** that `St4`/`StabilityFar` consume: on
`[0,S]` (any `S < T`) the vorticity is bounded by the *constant* `2M/(T-S)`. -/
theorem strip_bdd_of_repaired {α : NNReal} (C : ConstructedSolutionFixed α) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : S < C.T) :
    ∀ t ∈ Set.Icc 0 S, ∀ y : R3, ‖C.ω y t‖ ≤ 2 * C.M / (C.T - S) := by
  intro t ht y
  have htI : t ∈ Set.Ico 0 C.T := ⟨ht.1, lt_of_le_of_lt ht.2 hS⟩
  have hmem : t ∈ preWindow C.T := ⟨by linarith [ht.1], htI.2⟩
  have h1 : C.lam t * ‖C.ω y t‖ ≤ C.M := C.hBdd t hmem y
  have h2 : (C.T - t) / 2 ≤ C.lam t := C.hlam_low t htI
  have h3 : 0 < C.T - S := by linarith
  have h4 : 0 < C.lam t := lt_of_lt_of_le (by linarith [ht.2, hS]) h2
  have h4' : 0 ≤ C.lam t := le_of_lt h4
  have h5 : 0 < C.T - t := by linarith [ht.2, hS]
  have h6 : ‖C.ω y t‖ ≤ C.M / C.lam t := by
    rw [le_div_iff₀ h4]; linarith [h1]
  have h7 : C.M / C.lam t ≤ C.M / ((C.T - t) / 2) :=
    div_le_div_of_nonneg_left C.hM (by linarith [h5]) h2
  rw [le_div_iff₀ h3]
  calc ‖C.ω y t‖ * (C.T - S) ≤ (C.M / C.lam t) * (C.T - t) := by
        refine mul_le_mul h6 (by linarith [ht.2]) (by linarith [ht.1]) ?_
        exact div_nonneg C.hM h4'
    _ ≤ (C.M / ((C.T - t) / 2)) * (C.T - t) :=
        mul_le_mul_of_nonneg_right h7 (by linarith [h5])
    _ = 2 * C.M := by
        field_simp

/-! ## The model certificate for the repaired box pair -/

/-- **The repaired box pair is consistent — and the unrepaired one is not.**  For the honest
self-similar vorticity `Ω(x,t) = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p/λ̄(t)) x` with `|g| ≤ Cg`, the
repaired box `λ̄(t)·‖Ω(x,t)‖ ≤ 20p + Cg` and the `St5` lower bound hold *simultaneously*, whereas
the unrepaired pair `‖ω‖ ≤ M` with `hansatz` is contradictory
(`Obstruction.not_nonempty_constructedSolution`). -/
theorem selfSim_boxes {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    {lam : ℝ → ℝ} {T : ℝ} (hlam : ∀ t ∈ preWindow T, 0 < lam t)
    {c₀ α : ℝ}
    (hlow : ∀ t : ℝ, ∃ x : R3,
      c₀ * α ≤ ‖omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖) :
    (∀ t ∈ preWindow T, ∀ x : R3,
        lam t * ‖(lam t)⁻¹ • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖ ≤ 20 * p + Cg) ∧
      (∀ t ∈ preWindow T, ∃ x : R3,
        c₀ * α ≤ lam t * ‖(lam t)⁻¹ • omegaSz p g (Work.Cyl.rho x ^ p / lam t) x‖) :=
  ⟨fun t ht x => by
      rw [mul_norm_inv_smul (hlam t ht)]
      exact omegaSz_norm_le hp hp1 hCg hgbdd
        (div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg x) p) (hlam t ht).le) x,
    fun t ht => by
      obtain ⟨x, hx⟩ := hlow t
      exact ⟨x, by rw [mul_norm_inv_smul (hlam t ht)]; exact hx⟩⟩

/-! ## The certificates (the analogues of `Scaling.Patch.patch_verified`) -/

/-- **Certificate 1 — the repaired datum clause feeds the patched consumer.** -/
example {α : NNReal} (C : ConstructedSolutionFixed α) (hα1 : α ≤ 1) :
    Holder α (Work.SolutionDelivery.cutDatum C.L C.ωS) :=
  cutDatum_holder_of_holder C.hL hα1
    (Work.Stability.isBoundedFun_of_forall_norm_le C.ωS_bdd) C.ωS_holder

/-- **Certificate 2 — the patched datum construction** (`SolutionDelivery/Basic.lean` and
`DatumEuler.lean` go through with the repaired interface and no new hypothesis). -/
example {α : NNReal} (C : ConstructedSolutionFixed α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum C.L C.ωS)) ∧
      Work.LWP.EulerDataBS α
        (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum C.L C.ωS)) :=
  datumData_of_cut_of_holder C.lwp C.hL C.hM hα hα1 C.ωS_meas C.ωS_bdd C.ωS_holder
    C.ωS_div C.ωS_odd

/-- **Certificate 3 — the instantiation elaborates** (no extra hypothesis beyond the residual
data). -/
example {α : NNReal} (D : ConstructionDataFixed α) : ConstructedSolutionFixed α :=
  constructedSolutionFixed D

/-- **Certificate 4 — the repaired maximal-solution existence** (the patched body of
`Work.SolutionDelivery.exists_maximal_of_datum`). -/
example {α : NNReal} (C : ConstructedSolutionFixed α) (hα : 0 < (α : ℝ))
    (hα1 : (α : ℝ) ≤ 1) :
    ∃ T : ℝ, 0 < T ∧ Nonempty (Work.LWP.MaximalSolution α
      (Work.LWP.biotSavart (Work.SolutionDelivery.cutDatum C.L C.ωS)) T) :=
  exists_maximal_of_datum_of_holder C.lwp C.hL C.hM C.ωS_meas C.ωS_bdd C.ωS_holder hα hα1
    C.ωS_div C.ωS_odd

/-- **Certificate 5 — every field about the vorticity is a theorem.**  For any inhabitant of the
(residual) profile data, the vorticity-level fields of the interface hold. -/
example {α : NNReal} (P : ProfileData α) :
    (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |P.g z θ| ≤ P.Cg) ∧
      (∀ t : ℝ, ∀ y : R3, solVort P y t ≠ 0 → y ∈ Metric.closedBall 0 P.R) ∧
        (∀ t ∈ preWindow P.T, ∀ y : R3, P.lam t * ‖solVort P y t‖ ≤ P.M) ∧
          (∀ t ∈ preWindow P.T, ∀ y : R3,
            (P.lam t) ^ 2 * ‖timeDeriv (solVort P) y t‖ ≤ P.M₁) ∧
            (∀ t ∈ Set.Ico 0 P.T, ∃ x : R3,
              c₀star α * (α : ℝ) ≤ P.lam t * ‖solVort P x t‖) ∧
              (∀ t ∈ preWindow P.T, FiniteTimeSingularity.div (solVort P · t) = 0) ∧
                (∀ S : ℝ, 0 < S → S + 1 < P.T → ∃ H : ℝ, 0 ≤ H ∧
                  Work.StabilityFar.TimeHolderOnBall (α : ℝ) (solVort P) P.R S H) :=
  ⟨bdd_g P, fun t y hy => solVort_supp P t y hy, solVort_bdd P, solVort_bddDt P,
    solVort_hansatz P, solVort_div P, solVort_timeHolder P⟩

end Work.ConstructionInstance
