import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.LWP.VorticityAPI
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.ConstructionInstance.Patch =====
section

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


/-! ## The model certificate for the repaired box pair -/


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
end
end
-- ===== merged: Submission.Work.ConstructionInstance.solVort_timeHolder_Icc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The time-Hölder regularity of the constructed vorticity on the physical strip `[0,S]`.**

`Reduced.solVort_timeHolder` delivers the same statement for the *two-sided* window
`window S = Icc (-1) (S+1)`, which is legitimate only for strips with `S + 1 < T` (a window
straddling `T` cannot carry a uniform constant, finding E).  The challenge's regularity clause is
phrased on the *one-sided* strip `Icc 0 S`, `S < T`, so it needs the version where the mean value
theorem is applied to the convex set `Icc 0 S` itself: on that strip the modulation `λ̄` is
bounded below by a positive `m` (it is positive and continuous on `preWindow T = Ioo (-2) T`, and
`Icc 0 S` is a compact interval inside it), whence the weighted box
`λ̄(t)²‖∂ₜω‖ ≤ K(20p + Cg + Cg')` of `bddDt_selfSimVort` becomes the unweighted bound
`‖∂ₜω‖ ≤ K(20p + Cg + Cg')/m² =: Λ`; the mean value theorem then gives
`‖ω z t - ω z τ‖ ≤ Λ|t - τ| ≤ Λ·max S 1·|t - τ|^α` for `t, τ ∈ Icc 0 S`.

The three ingredients are `lam_pos_le_on_Icc`, `timeDeriv_selfSimVort_le_Icc` (the unweighted
`∂ₜ`-bound on the strip) and the mean value theorem on `Icc 0 S`
(`timeHolderOnBall_of_timeDeriv_le_Icc`); the differentiability of the slices is
`hasDerivAt_selfSimVort_slice`. -/
theorem solVort_timeHolder_Icc {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ S ∈ Set.Ioo (0 : ℝ) P.T, ∃ H : ℝ, 0 ≤ H ∧
      ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
        ∀ t ∈ Set.Icc 0 S, ∀ τ ∈ Set.Icc 0 S,
          ‖Work.ConstructionInstance.solVort P z t - Work.ConstructionInstance.solVort P z τ‖
            ≤ H * |t - τ| ^ (α : ℝ) := by
  intro S hS
  have hS0 : 0 ≤ S := le_of_lt hS.1
  have hST : S < P.T := hS.2
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := le_trans (abs_nonneg _) (bdd_g P 0 0 le_rfl hI0)
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  -- the strip `Icc 0 S` sits inside the half-window on which the `λ̄`-data is stated
  have hsub : Set.Icc (0 : ℝ) S ⊆ preWindow P.T :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- a uniform positive lower bound for the modulation on the strip
  obtain ⟨m, hmpos, hmle⟩ := lam_pos_le_on_Icc hS0 hST P.hlam P.hlamdif
  -- the resulting unweighted bound `Λ` on `∂ₜω`
  set Λ : ℝ := P.K * (20 * profExp α + P.Cg + P.Cg') / m ^ 2 with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    exact div_nonneg (mul_nonneg P.hK (by linarith)) (by positivity)
  -- differentiability of every time slice on the strip
  have hdiff : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
      ∀ s ∈ Set.Icc 0 S,
        HasDerivAt (fun t => solVort P z t)
          (FiniteTimeSingularity.timeDeriv (solVort P) z s) s := by
    intro z _hz s hs
    exact hasDerivAt_selfSimVort_slice (p := profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) P.hgdiff P.hlam P.hlamdif (hsub hs) z
  -- the uniform bound on `∂ₜω` on the strip
  have hbd : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) P.R,
      ∀ s ∈ Set.Icc 0 S, ‖FiniteTimeSingularity.timeDeriv (solVort P) z s‖ ≤ Λ := by
    intro z _hz s hs
    exact timeDeriv_selfSimVort_le_Icc (p := profExp α) hp hp1 (bdd_g P) P.hg2 P.hgdiff
      P.hK P.hlam P.hlamdif P.hlamd hmpos hsub hmle hs z
  obtain ⟨H, hH0, hH⟩ := timeHolderOnBall_of_timeDeriv_le_Icc (α := (α : ℝ)) (Λ := Λ)
    (R := P.R) (S := S) (ω := solVort P) hS0 P.hα hα1 hΛ hdiff hbd
  exact ⟨H, hH0, hH⟩

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.vorticity_biotSavart_solVort =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem vorticity_biotSavart_solVort {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T, ∀ x : Work.ConstructionInstance.R3,
      FiniteTimeSingularity.vorticity
          (Work.LWP.biotSavart (fun y => Work.ConstructionInstance.solVort P y t)) x
        = Work.ConstructionInstance.solVort P x t := by
  intro t ht x
  exact ((hlaw (fun y => solVort P y t) (solVort_integrable P t ht)
    (solVort_isBoundedFun P t ht) (fun x => congrFun (solVort_div P t ht) x)).1 x)

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.QuadPorts

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Commutation of `D_z` with the iterates of `D_θ` on the open strip

`Work.Spaces.quadU = (-1,∞) × (0,π/2)` is exactly the strip on which `SmoothQuad` is stated.
The two proofs below are the `SmoothQuad` counterpart of `Work.Spaces.DzDthIterCommOn` /
`Work.Spaces.Dth_DzIter_comm_eqOn`, which are stated for the analytic class `SmoothNbhd`: at
each step Clairaut (`Work.Spaces.Dz_Dth_comm`, which only needs `C²` at the point) pushes the
outer `D_z` past the `D_θ`, and the resulting functions are compared by the congruence lemmas
`Work.Spaces.pth_congr_of_isOpen` / `Work.Spaces.pz_congr_of_isOpen` for arbitrary open sets. -/

/-- On the open strip, `D_z` commutes with every iterate of `D_θ`. -/
theorem DzDthIterCommOn_quad {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) Work.Spaces.quadU := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]

/-- On the open strip, `D_z^b` commutes with `D_θ^a`. -/
theorem DzIter_DthIter_comm_quad {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_quad
          (Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-! ## The index shift `D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` -/

/-- `D_z^i (D_z f) = D_z^{i+1} f` (definitional, from `D_z^{i+b} = D_z^i ∘ D_z^b`). -/
private lemma DzIter_Dz (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- The index shift at the *interior* points of the quadrant, where Clairaut is available. -/
theorem mixed_Dz_shift_interior {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.quadU :=
    Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), hθ⟩
  have hDzf : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := by
    simpa only [Work.Spaces.mixed, Function.uncurry] using
      (DzIter_DthIter_comm_quad hDzf b a hy)
  have h2 : Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f :=
    DzIter_Dz b f
  have h3 : Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := by
    simpa only [Function.uncurry] using
      (DzIter_DthIter_comm_quad hf (b + 1) a hy).symm
  calc Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := h1
    _ = Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ := by rw [h2]
    _ = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := h3
    _ = Work.Spaces.mixed (b + 1) a f z θ := rfl

/-! ### The boundary cases: everything vanishes

At `z = 0` every `D_z`-iterate of positive order vanishes (the outer factor of `D_z` is `z`); at
an angle with `sin(2θ) = 0` every positive iterate of `D_θ` vanishes, hence so do the `D_z`-slices
of the resulting functions. -/

/-- At `z = 0`, every `D_z`-iterate of order `≥ 1` vanishes. -/
private lemma DzIter_succ_apply_zero (b : ℕ) (H : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.DzIter (b + 1) H 0 θ = 0 := by
  show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter b H) 0 θ = 0
  rw [zero_mul]

/-- If the `θ`-slice of `H` at `z = 0` vanishes identically, so do all of its `D_θ`-iterates. -/
private lemma DthIter_slice_zero_of_slice_zero (a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) :
    (fun θ' => Work.Spaces.DthIter a H 0 θ') = fun _ => (0 : ℝ) := by
  induction a with
  | zero => funext θ'; exact hH θ'
  | succ a ih =>
      funext θ'
      have hpth : Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0 := by
        show deriv (fun θ'' => Work.Spaces.DthIter a H 0 θ'') θ' = 0
        rw [ih]
        simp
      show Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0
      rw [hpth, mul_zero]

/-- If the `θ`-slice of `H` at a fixed angle vanishes identically in `z`, so do all of its
`D_z`-iterates. -/
private lemma DzIter_apply_of_zslice_zero (b : ℕ) {H : ℝ → ℝ → ℝ} {θ : ℝ}
    (hH : ∀ z' : ℝ, H z' θ = 0) : ∀ z : ℝ, Work.Spaces.DzIter b H z θ = 0 := by
  induction b with
  | zero => exact hH
  | succ b ih =>
      intro z
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0 := by
        show deriv (fun z' => Work.Spaces.DzIter b H z' θ) z = 0
        rw [show (fun z' => Work.Spaces.DzIter b H z' θ) = fun _ => (0 : ℝ) from funext ih]
        simp
      show z * Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0
      rw [hpz, mul_zero]

/-- At `z = 0`, a mixed derivative of a function whose `θ`-slice at `z = 0` vanishes is zero. -/
private lemma mixed_apply_zero_fst_of_slice_zero (b a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) (θ : ℝ) : Work.Spaces.mixed b a H 0 θ = 0 := by
  rcases b with _ | b
  · exact congrFun (DthIter_slice_zero_of_slice_zero a hH) θ
  · exact DzIter_succ_apply_zero b (Work.Spaces.DthIter a H) θ

/-- At an angle with `sin(2θ) = 0`, a mixed derivative of angular order `a ≥ 1` vanishes. -/
private lemma mixed_apply_of_sin_zero (b a : ℕ) (ha : 1 ≤ a) (H : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.mixed b a H z θ = 0 := by
  have hslice : ∀ z' : ℝ, Work.Spaces.DthIter a H z' θ = 0 := by
    intro z'
    rcases a with _ | a
    · exact absurd ha (by omega)
    · exact Work.Spaces.DthIter_succ_eq_zero_of_sin_eq_zero a H hs
  exact DzIter_apply_of_zslice_zero b hslice z

/-- **The index shift on the whole domain**:
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz ×ˢ Iθ`, for `f` smooth on the open quadrant.
At the interior points this is the commutation of `D_z` and `D_θ`; at `z = 0` and at the angular
endpoints both sides vanish. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDz0 : ∀ θ' : ℝ, Work.Spaces.Dz f 0 θ' = 0 := fun θ' => by
    show (0 : ℝ) * Work.Spaces.pz f 0 θ' = 0
    rw [zero_mul]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rcases a with _ | a
    · show Work.Spaces.DzIter b (Work.Spaces.Dz f) 0 θ = Work.Spaces.DzIter (b + 1) f 0 θ
      rw [DzIter_Dz]
    · rw [mixed_apply_zero_fst_of_slice_zero b (a + 1) hDz0 θ]
      exact (DzIter_succ_apply_zero b (Work.Spaces.DthIter (a + 1) f) θ).symm
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact mixed_Dz_shift_interior hf b a hzpos hθin
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rcases a with _ | a
      · show Work.Spaces.DzIter b (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (b + 1) f z θ
        rw [DzIter_Dz]
      · rw [mixed_apply_of_sin_zero b (a + 1) (by omega) (Work.Spaces.Dz f) hs]
        exact (mixed_apply_of_sin_zero (b + 1) (a + 1) (by omega) f hs).symm

/-! ## Pointwise domination of the `ℋⁿ`-integrand of `D_z f` -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`. -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α n (D_z f)` is a summand of `HkIntegrand α (n+1) f`**, with
the same weight: the pure summands by `D_z^i (D_z f) = D_z^{i+1} f`, the mixed summands by the
index shift `mixed_Dz_shift`.  Hence the pointwise domination of the integrands (this is the
`SmoothQuad` version of `Work.Coercivity.HkIntegrand_Dz_le`, which asks for the analytic class
`Work.Spaces.SmoothNbhd` and for `0 < α`). -/
theorem HkIntegrand_Dz_le_succ (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      ≤ Work.Spaces.HkIntegrand α (n + 1) f z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      = (∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (n + 1) f z θ
      = (∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le n
      (fun a => (Work.Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz i f])
  have h2 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dz_shift hf j i hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) :=
    Work.Coercivity.SumShiftZ_le n
      (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-! ## The membership `HkMem α n (D_z f)` -/

/-- **The `𝓗ⁿ`-membership of `D_z f`**, by domination of its integrand by the `(n+1)`-integrand
of `f`: `Work.FTS.LocData.HkMem_of_majorant` with `M = HkIntegrand α (n+1) f`, the smoothness
input being `continuousOn_HkIntegrand_smoothQuad` for `D_z f`. -/
theorem HkMem_Dz_quad (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (h : Work.Spaces.HkMem α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dz f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dz f)
      (Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf))
    h.1 h.2
    (fun z hz θ hθ => HkIntegrand_Dz_le_succ α n hf z θ hz hθ)

/-! ## The transport of the boundary traces -/

/-- **The boundary traces of `D_z f`** from those of `f`: the traces at order `(a,b)` of `D_z f`
are the traces at order `(a,b+1)` of `f`, because the mixed derivatives agree on the domain
(`mixed_Dz_shift`) and every one-sided limit is taken through points of the domain. -/
theorem BdryTraces_Dz (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dz f) := by
  intro a b hab
  obtain ⟨hzlim, hθlim⟩ := hbd a (b + 1) (by omega)
  -- the two filters `𝓝[>] 0`, `𝓝[<] π/2` count the open interval as an eventual set
  have hmemGT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsGT_basis_of_exists_gt ⟨π / 2, Real.pi_div_two_pos⟩).mem_of_mem Real.pi_div_two_pos
  have hmemLT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) :=
    (nhdsLT_basis_of_exists_lt ⟨0, by linarith [Real.pi_pos]⟩).mem_of_mem
      (by linarith [Real.pi_pos])
  constructor
  · intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    constructor
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [mixed_Dz_shift hf b a (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).1.congr' hev
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[atTop]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [mixed_Dz_shift hf b a (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).2.congr' hev
  · intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    constructor
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemGT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [mixed_Dz_shift hf b a hzIz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).1.congr' hev
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[<] (π / 2)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemLT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [mixed_Dz_shift hf b a hzIz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).2.congr' hev

/-! ## The port -/

theorem RegQ_dz (α : ℝ) {n : ℕ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dz f) := by
  obtain ⟨hsm, hmem, hbd⟩ := h
  exact ⟨Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hsm,
    HkMem_Dz_quad α n hsm hmem, BdryTraces_Dz α n hsm hbd⟩

end Work.FTS.CoercivityFix.QuadPorts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.AuxE2

theorem radS_contDiffOn_three (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (fun z => Work.FTS.CoercivityFix.Transfer.radS α f z) (Set.Ioi 0) := by
  -- `c α ≠ 0`, from `1/10 ≤ c α` (`Work.Spaces.c_bounds`)
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  -- the two rational `z`-factors are `C^∞` (hence `C⁴`) on `(0,∞)`
  have hampA : ContDiffOn ℝ 4 (ampA α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 4 (fun z => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) (Set.Ioi 0)
    exact (((contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_id).div
      ((contDiffOn_const (c := Work.Spaces.c α)).mul
        (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 2))
      (fun z hz => mul_ne_zero hc (pow_ne_zero 2 (by linarith [show (0 : ℝ) < z from hz]))))
  have hampB : ContDiffOn ℝ 4 (ampB α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 4 (fun z => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0)
    exact (((contDiffOn_const (c := (2 : ℝ))).mul (contDiffOn_id.pow 2)).div
      (((contDiffOn_const (c := (1 : ℝ))).add contDiffOn_id).pow 3)
      (fun z hz => pow_ne_zero 3 (by linarith [show (0 : ℝ) < z from hz])))
  -- hence their `z`-multiples `dAmpA α` and `dAmpB α / c α`, too
  have hdA : ContDiffOn ℝ 3 (dAmpA α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 3 (fun z => z * deriv (ampA α) z) (Set.Ioi 0)
    exact contDiffOn_id.mul (hampA.deriv_of_isOpen isOpen_Ioi (by norm_num))
  have hdB : ContDiffOn ℝ 3 (fun z => dAmpB α z / Work.Spaces.c α) (Set.Ioi 0) := by
    change ContDiffOn ℝ 3 (fun z => z * deriv (ampB α) z / Work.Spaces.c α) (Set.Ioi 0)
    exact (contDiffOn_id.mul (hampB.deriv_of_isOpen isOpen_Ioi (by norm_num))).div_const _
  -- the analytic input: `L₁₂ f` is `C³` and its derivative is `C³`
  have hL : ContDiffOn ℝ 3 (Work.Coercivity.L12f f) (Set.Ioi 0) := hA.of_le (by norm_num)
  have hLd : ContDiffOn ℝ 3 (deriv (Work.Coercivity.L12f f)) (Set.Ioi 0) :=
    hA.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have key : ContDiffOn ℝ 3
      (fun z => -dAmpA α z * Work.Coercivity.L12f f z
        - ampA α z * (z * deriv (Work.Coercivity.L12f f) z)
        + (dAmpB α z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) (Set.Ioi 0) :=
    ((hdA.neg.mul hL).sub (hampA.of_le (by norm_num) |>.mul (contDiffOn_id.mul hLd))).add
      (hdB.mul contDiffOn_const)
  exact key.congr (fun z _ => by simp only [radS, dAmpA, dAmpB])

end Work.FTS.CoercivityFix.Transfer.AuxE2
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkSq_add_le_of_contDiffOn_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AlphaRateEstEllT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The open quadrant `(0,∞) × (0,π/2)` of the smoothness hypotheses. -/
private abbrev quadV : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## The `θ`-identity for the sum at levels `≤ k-1`

Both summands are `C^{k-1}` there, so the honest linearity of the totalised `D_θ^i` applies. -/


/-! ## The pointwise slot estimate -/


/-! ## The pointwise integrand estimate -/


/-! ## The statement -/


end Work.FTS.EllipticEst.Cores.AlphaRateEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The algebraic core -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Finite-order additivity of the iterated operators on the open quadrant -/

/-- The `z`-slice of a function that is `C^m` on the open quadrant is differentiable in `z`. -/
lemma differentiableAt_zslice {G : ℝ → ℝ → ℝ} {m : ℕ}
    (hG : ContDiffOn ℝ m (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' => G z' θ) z := by
  have hslice : ContDiffOn ℝ m (fun z' => G z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin
      (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) hG ⟨h1, h2⟩
  have h1' : ContDiffOn ℝ 1 (fun z' => G z' θ) (Set.Ioi 0) :=
    hslice.of_le (by exact_mod_cast hm)
  exact (h1'.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)

/-- The `θ`-slice of a function that is `C^m` on the open quadrant is differentiable in `θ`. -/
lemma differentiableAt_thslice {G : ℝ → ℝ → ℝ} {m : ℕ}
    (hG : ContDiffOn ℝ m (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hslice : ContDiffOn ℝ m (fun θ' => G z θ') (Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin
      (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) hG hz
  have h1' : ContDiffOn ℝ 1 (fun θ' => G z θ') (Set.Ioo 0 (π / 2)) :=
    hslice.of_le (by exact_mod_cast hm)
  exact (h1'.contDiffAt (isOpen_Ioo.mem_nhds ⟨h1, h2⟩)).differentiableAt (by simp)

/-- **Additivity of the iterated operator `D_z^j`** for data that are `C^m` on the open
quadrant, at orders `j ≤ m`. -/
theorem DzIter_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j ≤ m, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro _ z θ _ _ _; rfl
  | succ n ih =>
      intro hn z θ hz h1 h2
      have hn' : n ≤ m := by omega
      have hlt : n < m := by omega
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hn' z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        differentiableAt_zslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hf n hn')
          (by omega) hz h1 h2
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        differentiableAt_zslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hg n hn')
          (by omega) hz h1 h2
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ
            + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **Additivity of the iterated operator `D_θ^i`** for data that are `C^m` on the open
quadrant, at orders `i ≤ m`. -/
theorem DthIter_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i ≤ m, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  intro i
  induction i with
  | zero => intro _ z θ _ _ _; rfl
  | succ n ih =>
      intro hn z θ hz h1 h2
      have hn' : n ≤ m := by omega
      have hlt : n < m := by omega
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)] with θ' hθ'
        exact ih hn' z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        differentiableAt_thslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hf n hn')
          (by omega) hz h1 h2
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        differentiableAt_thslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hg n hn')
          (by omega) hz h1 h2
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ'
            + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- **Additivity of the mixed operators `D_z^j D_θ^i`** for data that are `C^m` on the open
quadrant, at orders `i + j ≤ m`. -/
theorem mixed_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j i, i + j ≤ m → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro j i hij z θ hz h1 h2
  have hi : i ≤ m := by omega
  have hcongr := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
    (fun z θ hz' h1' h2' => DthIter_add_fin hf hg i hi z θ hz' h1' h2') z θ hz h1 h2
  have hf' : ContDiffOn ℝ (m - i) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hf i hi
  have hg' : ContDiffOn ℝ (m - i) (Function.uncurry (Work.Spaces.DthIter i g))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hg i hi
  have hadd := DzIter_add_fin hf' hg' j (by omega) z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## The pointwise inequality -/

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z, θ)` for the indices that occur in `HkIntegrand α k`. -/
private lemma HkIntegrand_add_le_pt_fin (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i ≤ k, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ j i, i + j ≤ k → Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hij : p.1 + p.2 ≤ k := (Finset.mem_filter.mp hp).2.2
      rw [hm p.2 p.1 hij]
      ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The theorem -/

/-- **Subadditivity of the `ℋ^k`-integrand for data smooth to order `k`.**  For `f`, `g` of
class `C^k` on the open quadrant and `(z,θ)` in the open quadrant,

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`.

This is the honest (finite-smoothness) form of `HkIntegrand_add_le_open`, which is what the
straightened datum `Ψ + Gsing α F · sin 2θ` of Theorem `RemovingL12` can be fed. -/
theorem HkIntegrand_add_le_of_contDiffOn (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z θ hz h1 h2
  exact HkIntegrand_add_le_pt_fin α k f g z θ
    (fun i hi => DzIter_add_fin hf hg i hi z θ hz h1 h2)
    (fun j i hij => mixed_add_fin hf hg j i hij z θ hz h1 h2)


/-! ## Additivity of `∂_θ` and of its iterates, on the open quadrant -/

/-- **`pthIter` drops `l` orders of differentiability.** -/
theorem contDiffOn_pthIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {m : ℕ}
    (h : ContDiffOn ℝ m (Function.uncurry G) U) :
    ∀ l ≤ m, ContDiffOn ℝ (m - l : ℕ) (Function.uncurry (Work.Spaces.pthIter l G)) U := by
  intro l
  induction l with
  | zero => intro _; simpa using h
  | succ l ih =>
      intro hl
      have hl' : l ≤ m := by omega
      have h1 : ContDiffOn ℝ (m - l : ℕ) (Function.uncurry (Work.Spaces.pthIter l G)) U := ih hl'
      have h2 : ContDiffOn ℝ (m - l - 1 + 1 : ℕ)
          (Function.uncurry (Work.Spaces.pthIter l G)) U := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m - l)]; exact h1
      have h3 : ContDiffOn ℝ (m - l - 1 : ℕ)
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter l G))) U :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin hU h2
      have heq : m - (l + 1) = m - l - 1 := by omega
      rw [heq, Work.Spaces.pthIter_succ]
      exact h3

/-- **`pth` is additive on `Q0`** for data that are `C^1` in `θ` there (the totalised `deriv` is
additive at points where both slices are differentiable). -/
theorem pth_add_on_Q0 {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hdf : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    differentiableAt_thslice hf hm hz h1 h2
  have hdg : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    differentiableAt_thslice hg hm hz h1 h2
  show deriv (fun θ' => (fun z θ => f z θ + g z θ) z θ') θ = _
  rw [show (fun θ' => (fun z θ => f z θ + g z θ) z θ') = fun θ' => f z θ' + g z θ' from rfl]
  exact deriv_add hdf hdg

/-- **`pthIter i` is additive on `Q0`** (`1 ≤ i ≤ m`) for data that are `C^m` in `θ` there. -/
theorem pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i, 1 ≤ i → i ≤ m → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter i f z θ + Work.Spaces.pthIter i g z θ := by
  intro i
  induction i with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ n ih =>
      intro _ hn z θ hz h1 h2
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simpa using pth_add_on_Q0 hf hg (by omega) z θ hz h1 h2
      · have hnle : n ≤ m := by omega
        have hfn : ContDiffOn ℝ (m - n : ℕ) (Function.uncurry (Work.Spaces.pthIter n f))
            Work.FTS.EllipticEst.Q0 := contDiffOn_pthIter_fin isOpen_Q0 hf n hnle
        have hgn : ContDiffOn ℝ (m - n : ℕ) (Function.uncurry (Work.Spaces.pthIter n g))
            Work.FTS.EllipticEst.Q0 := contDiffOn_pthIter_fin isOpen_Q0 hg n hnle
        have hev : (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
            =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ'
              + Work.Spaces.pthIter n g z θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
            with θ' hθ'
          exact ih hnpos hnle z θ' hz hθ'.1 hθ'.2
        show deriv (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ') θ
            = deriv (fun θ' => Work.Spaces.pthIter n f z θ') θ
              + deriv (fun θ' => Work.Spaces.pthIter n g z θ') θ
        rw [hev.deriv_eq]
        simpa only [Work.Spaces.pth] using pth_add_on_Q0 hfn hgn (by omega) z θ hz h1 h2

end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.eslHkMemPthTwoZsq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_θ²(z²∂_z²Ψ) ∈ ℋ⁰` for a datum of the weak class `EllWeakPos α 2 F Ψ`

This module proves `Work.FTS.EllipticEst.H2W.eslHkMemPthTwoZsq`: for every datum
`(F, Ψ)` of the weak hypothesis class `TT.EllWeakPos α 2 F Ψ` (no hypothesis on `α` is
needed), the angular second derivative of the radial datum `z²∂_z²Ψ` is honest at level `0`:

  `HkMem α 0 (∂_θ²(z²∂_z²Ψ))`.

Equivalently — by Clairaut on the open quadrant, where `Ψ` is `C^∞` — the function is
`z² ∂_z²(∂_θ²Ψ) = D_z² H - D_z H` with `H = ∂_θ²Ψ`, and `z²∂_z² = D_z² - D_z`.  The
honesty is therefore read off from the two radial summands

  `(D_z H · w/sin(2θ)^{η/2})²`, `(D_z² H · w/sin(2θ)^{η/2})²`

of the *level-`2`* `ℋ`-integrand of `H`, which is honest by the hypothesis
`TT.EllWeakPos.memB : HkMem α 2 (∂_θ²Ψ)` (`RPFresh.excess_zsummand_mem`), and the pointwise
identity `deriv_deriv_zsq_pzIter2_eq` of `H2W.aSliceHonest`.  The passage from the pointwise
domination to `HkMem α 0` is `RPFresh.HkMem_zero_of_majorant`; the boundary points `z = 0`
and `θ ∈ {0, π/2}`, where the identity is not available, are the junk points of the integrand
(`HkIntegrand_zero_zero`, `HkIntegrand_zero_theta_zero`, `HkIntegrand_zero_theta_pi`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Honesty of `∂_θ²(z²∂_z²Ψ)` at level `0`.**  From smoothness of `Ψ` on the open
quadrant and the honesty of `H = ∂_θ²Ψ` at level `2`, the angular second derivative of the
radial datum `z²∂_z²Ψ` belongs to `ℋ⁰`. -/
theorem HkMem_pthIter2_zsq_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hmemB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
  have hSH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter_H2W hSΨ 2
  -- the two radial summands of the level-`2` integrand of `H = ∂_θ²Ψ`
  have hb1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
      ((hSH.DzIter 1).continuousOn) hmemB (by norm_num)
  have hb2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
      ((hSH.DzIter 2).continuousOn) hmemB (by norm_num)
  -- continuity of the slice function on the open quadrant (via the Clairaut identity)
  have hcontG : ContinuousOn
      (Function.uncurry (fun z θ =>
        deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hbase : ContinuousOn
        (fun p : ℝ × ℝ =>
          p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_fst.pow 2).mul ((hSH.pzIter 2).continuousOn)
    refine hbase.congr ?_
    rintro ⟨z, θ⟩ hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact deriv_deriv_zsq_pzIter2_Qop hSΨ hz ⟨hθ0, hθ1⟩
  -- the target function unfolds definitionally to the explicit `deriv` form
  change Work.Spaces.HkMem α 0
    (fun z θ => deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
  refine Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_of_majorant (α := α)
    (f := fun z θ =>
      deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
    (M := fun z θ =>
      2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ)
    hcontG ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z hz
    exact ((hb2.1 z hz).const_mul 2).add ((hb1.1 z hz).const_mul 2)
  · -- the `z`-integral of the majorant is integrable
    have h' := (hb2.2.const_mul 2).add (hb1.2.const_mul 2)
    refine h'.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Pi.add_apply, MeasureTheory.integral_add ((hb2.1 z hz).const_mul 2)
      ((hb1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  · -- the pointwise domination on the closed quadrant
    intro z hz θ hθ
    have hMnn : 0 ≤ 2 * Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
        + 2 * Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
      have h₁ := Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
      have h₂ := Work.Spaces.HkIntegrand_nonneg α 0
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
      linarith
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz_eq | hz_pos
    · -- `z = 0`
      subst hz_eq
      rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_z]
      exact hMnn
    · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ_pos
      · -- `θ = 0`
        subst hθ_eq
        rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_zero]
        exact hMnn
      · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ_lt
        · -- `θ = π/2`
          subst hθ_eq
          rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_theta_pi]
          exact hMnn
        · -- interior: use the pointwise identity and AM–GM
          rw [Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
            deriv_deriv_zsq_pzIter2_eq hSΨ hz_pos ⟨hθ_pos, hθ_lt⟩,
            Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq,
            Work.FTS.EllipticEst.H2W.AeDataAofAux.HkIntegrand_zero_eq]
          set A := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hA
          set B := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hB
          set c := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
          nlinarith [sq_nonneg (A * c + B * c), sq_nonneg (A * c), sq_nonneg (B * c)]

/-- The requested lemma: for every datum of the weak class `TT.EllWeakPos α 2 F Ψ`, the
function `∂_θ²(z²∂_z²Ψ)` is honest at level `0`. -/
theorem eslHkMemPthTwoZsq (α : ℝ) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
  HkMem_pthIter2_zsq_pzIter2 ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth)
    h.memB

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.FamEAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Plumbing: smoothness, congruence and linearity of the plain iterated derivatives -/

/-- `pzIter i f z θ` is the `i`-fold iterate of `deriv` applied to the `z`-slice. -/
theorem pzIter_apply_eq_iterate_deriv (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i f z θ = deriv^[i] (fun z' => f z' θ) z := by
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, Function.iterate_succ_apply']
      congr 1
      funext z'
      exact ih z'

/-- `pthIter i f z θ` is the `i`-fold iterate of `deriv` applied to the `θ`-slice. -/
theorem pthIter_apply_eq_iterate_deriv (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter i f z θ = deriv^[i] (fun θ' => f z θ') θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pth, Function.iterate_succ_apply']
      congr 1
      funext θ'
      exact ih θ'

/-- `ContDiffOn` is stable under the plain `z`-partial, losing one order. -/
theorem famAux_contDiffOn_uncurry_pz_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (hX : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pz X)) V := by
  have hdiff : DifferentiableOn ℝ (Function.uncurry X) V :=
    hX.differentiableOn (by simp)
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fderiv ℝ (Function.uncurry X)) V :=
    hX.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry X) p) (1, 0)) V :=
    h1.clm_apply contDiffOn_const
  refine h2.congr (fun p hp => ?_)
  exact deriv_slice_fst _ _ _ ((hdiff.differentiableAt (hV.mem_nhds hp)))

/-- Iterated version: the `i`-th plain `z`-partial loses `i` orders of smoothness. -/
theorem famAux_contDiffOn_uncurry_pzIter_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i < N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter i X)) V := by
  intro i
  induction i with
  | zero => intro N hN h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pz (Work.Spaces.pzIter n X))) V :=
        famAux_contDiffOn_uncurry_pz_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]; exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pzIter_succ] using h2

/-- `ContDiffOn` is stable under the plain `θ`-partial, losing one order. -/
theorem famAux_contDiffOn_uncurry_pth_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (hX : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pth X)) V := by
  have hdiff : DifferentiableOn ℝ (Function.uncurry X) V :=
    hX.differentiableOn (by simp)
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fderiv ℝ (Function.uncurry X)) V :=
    hX.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry X) p) (0, 1)) V :=
    h1.clm_apply contDiffOn_const
  refine h2.congr (fun p hp => ?_)
  exact deriv_slice_snd _ _ _ ((hdiff.differentiableAt (hV.mem_nhds hp)))

/-- Iterated version: the `i`-th plain `θ`-partial loses `i` orders of smoothness. -/
theorem famAux_contDiffOn_uncurry_pthIter_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i < N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter i X)) V := by
  intro i
  induction i with
  | zero => intro N hN h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter n X))) V :=
        famAux_contDiffOn_uncurry_pth_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]; exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pthIter_succ] using h2

/-- The `z`-slice of a `C^n` function is `C^n` on the corresponding `z`-section. -/
theorem contDiffOn_slice_z {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {θ : ℝ} :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun z => X z θ) {z | (z, θ) ∈ V} := by
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun z : ℝ => (z, θ)) {z | (z, θ) ∈ V} :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  exact (hX.comp h1 fun z hz => hz)


/-- A `C^n` (`n ≥ 1`) function on an open set is differentiable in `z` at each point. -/
theorem differentiableAt_slice_z_of_contDiffOn {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (hn : 1 ≤ n)
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => X z' θ) z := by
  have h1 : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (hX.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by simp; omega)
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using h1.comp z h2

/-- A `C^n` (`n ≥ 1`) function on an open set is differentiable in `θ` at each point. -/
theorem differentiableAt_slice_th_of_contDiffOn {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (hn : 1 ≤ n)
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => X z θ') θ := by
  have h1 : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (hX.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by simp; omega)
  have h2 : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using h1.comp θ h2

/-! ## Congruence of the plain iterated derivatives on an open set -/

theorem pzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter i u))
      (Function.uncurry (Work.Spaces.pzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih => exact fun p hp => Work.Spaces.pz_congr_of_isOpen hV ih hp

theorem pthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter i u))
      (Function.uncurry (Work.Spaces.pthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih => exact fun p hp => Work.Spaces.pth_congr_of_isOpen hV ih hp

/-! ## Linear algebra of the iterated derivatives -/

theorem iterate_deriv_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv^[i] (fun x => c * f x) x = c * deriv^[i] f x := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun x => c * f x) = fun x => c * deriv^[n] f x := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_const_mul_field]

theorem iterate_deriv_mul_const (i : ℕ) (f : ℝ → ℝ) (c : ℝ) (x : ℝ) :
    deriv^[i] (fun x => f x * c) x = deriv^[i] f x * c := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun x => f x * c) = fun x => deriv^[n] f x * c := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_mul_const_field]


/-- The iterated `z`-derivative of a product of a `z`-only and a `θ`-only function. -/
theorem pzIter_mul_zonly_thetaonly (i : ℕ) (f : ℝ → ℝ) (h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i (fun z' θ' => f z' * h θ') z θ = deriv^[i] f z * h θ := by
  rw [pzIter_apply_eq_iterate_deriv]
  have : (fun z' : ℝ => f z' * h θ) = (fun z' : ℝ => (fun z'' => f z'') z' * h θ) := rfl
  rw [this, iterate_deriv_mul_const]

/-- The iterated `θ`-derivative of a product of a `z`-only and a `θ`-only function. -/
theorem pthIter_mul_zonly_thetaonly (j : ℕ) (f : ℝ → ℝ) (h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter j (fun z' θ' => f z' * h θ') z θ = f z * deriv^[j] h θ := by
  rw [pthIter_apply_eq_iterate_deriv]
  have : (fun θ' : ℝ => f z * h θ') = (fun θ' : ℝ => f z * (fun θ'' => h θ'') θ') := rfl
  rw [this, iterate_deriv_const_mul]


/-! ## Linearity of the iterated derivatives over differences and finite sums -/

theorem pzIter_sub_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ i : ℕ, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V →
      Set.EqOn (Function.uncurry (Work.Spaces.pzIter i (fun z θ => X z θ - Y z θ)))
        (Function.uncurry (fun z θ => Work.Spaces.pzIter i X z θ
          - Work.Spaces.pzIter i Y z θ)) V := by
  intro i
  induction i with
  | zero => intro _ _ p hp; rfl
  | succ n ih =>
      intro hX hY p hp
      have hX' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V :=
        hX.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hY' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V :=
        hY.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ z' : ℝ in 𝓝 p.1, (z', p.2) ∈ V :=
        (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => X z θ - Y z θ) z' p.2)
          =ᶠ[𝓝 p.1] (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2
            - Work.Spaces.pzIter n Y z' p.2) := by
        filter_upwards [hsec] with z' hz'
        exact ih hX' hY' hz'
      have hcX : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n X)) V := by
        have h := famAux_contDiffOn_uncurry_pzIter_le hV n (n + 1) (by omega) hX'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdX : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2) p.1 :=
        differentiableAt_slice_z_of_contDiffOn hV (n := 1) le_rfl hcX hp
      have hcY : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n Y)) V := by
        have h := famAux_contDiffOn_uncurry_pzIter_le hV n (n + 1) (by omega) hY'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdY : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) p.1 :=
        differentiableAt_slice_z_of_contDiffOn hV (n := 1) le_rfl hcY hp
      show deriv (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => X z θ - Y z θ) z' p.2) p.1
        = deriv (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2) p.1
          - deriv (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) p.1
      rw [hev.deriv_eq,
        show (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2 - Work.Spaces.pzIter n Y z' p.2)
          = (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2)
            - (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) from rfl,
        deriv_sub hdX hdY]

theorem pthIter_sub_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ i : ℕ, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V →
      Set.EqOn (Function.uncurry (Work.Spaces.pthIter i (fun z θ => X z θ - Y z θ)))
        (Function.uncurry (fun z θ => Work.Spaces.pthIter i X z θ
          - Work.Spaces.pthIter i Y z θ)) V := by
  intro i
  induction i with
  | zero => intro _ _ p hp; rfl
  | succ n ih =>
      intro hX hY p hp
      have hX' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V :=
        hX.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hY' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V :=
        hY.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ θ' : ℝ in 𝓝 p.2, (p.1, θ') ∈ V :=
        (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => X z θ - Y z θ) p.1 θ')
          =ᶠ[𝓝 p.2] (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ'
            - Work.Spaces.pthIter n Y p.1 θ') := by
        filter_upwards [hsec] with θ' hθ'
        exact ih hX' hY' hθ'
      have hcX : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n X)) V := by
        have h := famAux_contDiffOn_uncurry_pthIter_le hV n (n + 1) (by omega) hX'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdX : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ') p.2 :=
        differentiableAt_slice_th_of_contDiffOn hV (n := 1) le_rfl hcX hp
      have hcY : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n Y)) V := by
        have h := famAux_contDiffOn_uncurry_pthIter_le hV n (n + 1) (by omega) hY'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdY : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') p.2 :=
        differentiableAt_slice_th_of_contDiffOn hV (n := 1) le_rfl hcY hp
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => X z θ - Y z θ) p.1 θ') p.2
        = deriv (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ') p.2
          - deriv (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') p.2
      rw [hev.deriv_eq,
        show (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ' - Work.Spaces.pthIter n Y p.1 θ')
          = (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ')
            - (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') from rfl,
        deriv_sub hdX hdY]



/-! ## The normalising constant of the `8`-fold antiderivative, and the monomial facts -/

/-- The product of the eight falling-factorial denominators attached to the exponents `(a,b)`. -/
def Kf (a b : ℕ) : ℝ :=
  (((a : ℝ) + 1) * ((a : ℝ) + 2) * ((a : ℝ) + 3) * ((a : ℝ) + 4))
    * (((b : ℝ) + 1) * ((b : ℝ) + 2) * ((b : ℝ) + 3) * ((b : ℝ) + 4))

theorem Kf_pos (a b : ℕ) : 0 < Kf a b := by
  unfold Kf; positivity




/-! ## The `8`-fold antiderivative of a monomial sum -/


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Inhabit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## The zero function: degenerate computations -/

/-- The iterated `D_z`-derivative of the zero function is zero. -/
theorem DzIter_zero_fun (i : ℕ) : Spaces.DzIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Spaces.DzIter_succ, ih]
    funext z θ
    simp [Spaces.Dz, Spaces.pz]

/-- The iterated `D_θ`-derivative of the zero function is zero. -/
theorem DthIter_zero_fun (i : ℕ) : Spaces.DthIter i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Spaces.DthIter_succ, ih]
    funext z θ
    simp [Spaces.Dth, Spaces.pth]

/-- Every mixed `D`-derivative of the zero function is zero. -/
theorem mixed_zero_fun (j i : ℕ) : Spaces.mixed j i (fun _ _ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  rw [Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zero_fun (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Spaces.HkIntegrand α k (fun _ _ => (0 : ℝ)) z θ = 0 := by
  simp [Spaces.HkIntegrand, DzIter_zero_fun, mixed_zero_fun]

/-- The `ℋ^k`-norm squared of the zero function vanishes. -/
theorem HkSq_zero_fun (α : ℝ) (k : ℕ) : Spaces.HkSq α k (fun _ _ => (0 : ℝ)) = 0 := by
  simp [Spaces.HkSq, HkIntegrand_zero_fun]


/-- The operator `L₁₂` of the fundamental model vanishes on the zero function. -/
theorem L12_zero_fun (z : ℝ) : Construction.L12 (fun _ _ => (0 : ℝ)) z = 0 := by
  simp [Construction.L12, Construction.L12dens, FM.L12, FM.L12dens]

/-! ## Inhabitation of the data and regularity structures -/




/-! ## The Galerkin scheme is nondegenerate -/






end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.ZsummandQL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-- The majorant `zsVQ` of the `Z`-summand is square integrable, with

`|zsVQ|²_{L²} ≤ 10¹²/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}`.

Each summand of `zsVQ` is `|C(i,b)|·√(zsGamQ b)·|D_z^{zsIdxQ i b}(zsFunQ f g b)·w/sin(2θ)^{η/2}|`:
its `L²`-norm is bounded by `HkSq` of the retained factor (`L2Sq_DzIter_le_HkSq`) and the finitely
many summands are combined with the Cauchy–Schwarz estimate of
`Work.Spaces.HPRZ.L2Mem_L2Sq_finset_sum_le`. -/
theorem ZsummandQL2 (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (hγ : 0 < Work.Spaces.gam α - 1)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (i : ℕ) (hi : i ≤ 4)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.L2Mem (Work.FTS.H2.HQ.zsVQ α f g Cf Cg i)
      ∧ Work.Spaces.L2Sq (Work.FTS.H2.HQ.zsVQ α f g Cf Cg i)
        ≤ 10 ^ 12 / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  -- ## Step 1: membership of the retained pieces
  have hpiece : ∀ b ∈ Finset.range (i + 1), L2Mem (zsFbQ f g i b) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    by_cases hb2 : b ≤ 2
    · have h := L2Mem_light_quad α g hg hmg (i - b) (by omega)
      rw [zsFbQ_eq f g i b hb2]
      exact Work.Spaces.HPRZ.L2Mem_abs h
    · have h := L2Mem_light_quad α f hf hmf b (by omega)
      rw [zsFbQ_eq' f g i b hb2]
      exact Work.Spaces.HPRZ.L2Mem_abs h
  -- ## Step 2: the two a.e. strong measurability hypotheses for the sum
  have hslice_aesm : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) ^ 2) (volume.restrict Iθ) := by
    intro z hz
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) (volume.restrict Iθ) :=
      Work.Spaces.HPRZ.aesm_finset_sum (Finset.range (i + 1))
        (f := fun b (θ : ℝ) => zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
        (fun b _ => by
          by_cases hb2 : b ≤ 2
          · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter (i - b) g z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_slice g hg (i - b) hz)
            rw [zsFbQ_eq f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b)
          · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter b f z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_slice f hf b hz)
            rw [zsFbQ_eq' f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b))
    exact h1.pow 2
  have houter_aesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
    have hj : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b p.1 p.2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
      Work.Spaces.HPRZ.aesm_finset_sum (Finset.range (i + 1))
        (f := fun b (p : ℝ × ℝ) => zsAAQ α f g Cf Cg i b * zsFbQ f g i b p.1 p.2)
        (fun b _ => by
          by_cases hb2 : b ≤ 2
          · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter (i - b) g p.1 p.2
                * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
                ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_prod g hg (i - b))
            rw [zsFbQ_eq f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b)
          · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter b f p.1 p.2
                * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
                ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_prod f hf b)
            rw [zsFbQ_eq' f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b))
    exact (hj.pow 2).integral_prod_right'
  -- ## Step 3: the Cauchy–Schwarz assembly
  have hV := Work.Spaces.HPRZ.L2Mem_L2Sq_finset_sum_le (Finset.range (i + 1))
    (zsFbQ f g i) (zsAAQ α f g Cf Cg i) hpiece hslice_aesm houter_aesm
  -- ## Step 4: the squared `L²`-norm of each piece
  have hpiecebd : ∀ b ∈ Finset.range (i + 1),
      (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)
        ≤ (i.choose b : ℝ) ^ 2
          * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have haa : (zsAAQ α f g Cf Cg i b) ^ 2
        = (i.choose b : ℝ) ^ 2 * zsGamQ α f g Cf Cg b := by
      rw [zsAAQ_apply, mul_pow, sq_abs]
      congr 1
      exact Real.sq_sqrt (zsGamQ_nonneg α f g Cf Cg hγ hCf hCg b)
    have hL2 : L2Sq (zsFbQ f g i b) ≤ HkSq α 4 (zsFunQ f g b) := by
      by_cases hb2 : b ≤ 2
      · have h := L2Sq_DzIter_le_HkSq α 4 g hmg (i - b) (by omega)
        have h' : L2Sq (fun z θ => |DzIter (i - b) g z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 g := by
          rw [Work.Spaces.HPRZ.L2Sq_abs]; exact h
        rw [zsFbQ_eq f g i b hb2, zsFunQ_eq f g b hb2]
        exact h'
      · have h := L2Sq_DzIter_le_HkSq α 4 f hmf b (by omega)
        have h' : L2Sq (fun z θ => |DzIter b f z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 f := by
          rw [Work.Spaces.HPRZ.L2Sq_abs]; exact h
        rw [zsFbQ_eq' f g i b hb2, zsFunQ_eq' f g b hb2]
        exact h'
    have hΓHk : zsGamQ α f g Cf Cg b * HkSq α 4 (zsFunQ f g b)
        ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
      by_cases hb2 : b ≤ 2
      · rw [zsGamQ_eq α f g Cf Cg b hb2, zsFunQ_eq f g b hb2]
        have hle : Cf / (gam α - 1) ≤ (Cf + Cg) / (gam α - 1) :=
          div_le_div_of_nonneg_right (by linarith) hγ.le
        calc Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
            ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (HkSq_nonneg α 4 f))
                (HkSq_nonneg α 4 g)
          _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := rfl
      · rw [zsGamQ_eq' α f g Cf Cg b hb2, zsFunQ_eq' f g b hb2]
        have hle : Cg / (gam α - 1) ≤ (Cf + Cg) / (gam α - 1) :=
          div_le_div_of_nonneg_right (by linarith) hγ.le
        calc Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
            ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 g * HkSq α 4 f :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (HkSq_nonneg α 4 g))
                (HkSq_nonneg α 4 f)
          _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
    calc (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)
        ≤ ((i.choose b : ℝ) ^ 2 * zsGamQ α f g Cf Cg b) * HkSq α 4 (zsFunQ f g b) := by
          rw [haa]
          exact mul_le_mul_of_nonneg_left hL2
            (mul_nonneg (sq_nonneg _) (zsGamQ_nonneg α f g Cf Cg hγ hCf hCg b))
      _ = (i.choose b : ℝ) ^ 2
            * (zsGamQ α f g Cf Cg b * HkSq α 4 (zsFunQ f g b)) := by ring
      _ ≤ (i.choose b : ℝ) ^ 2
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_left hΓHk (sq_nonneg _)
  have hsum : (∑ b ∈ Finset.range (i + 1),
        (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b))
      ≤ (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
        * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
    calc (∑ b ∈ Finset.range (i + 1),
          (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b))
        ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          Finset.sum_le_sum hpiecebd
      _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          (Finset.sum_mul ..).symm
  -- ## Step 5: the numerical coefficient
  have hcoef : ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
      ≤ 10 ^ 12 := by
    have h := Work.Spaces.HPRZ.zs_coeff_bound i hi
    linarith [h]
  have hMnn : 0 ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hγ.le) (HkSq_nonneg α 4 f))
      (HkSq_nonneg α 4 g)
  refine ⟨?_, ?_⟩
  · show L2Mem (fun z θ => ∑ b ∈ Finset.range (i + 1),
      zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
    exact hV.1
  · show L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
      ≤ 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g
    calc L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
        ≤ ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1),
            (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)) := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hV.2
      _ ≤ ((i : ℝ) + 1) * ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2))
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by ring
      _ ≤ 10 ^ 12 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_right hcoef hMnn
      _ = 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.ZsummandQPtwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-- **The pointwise bound of the pure `D_z`-summand of the product rule.**

On the open quadrant, the light-weighted `D_z^i`-slot of the product `f·g`
(`i ≤ 4`) is dominated by the majorant `zsVQ`: the Leibniz expansion is split,
each summand keeps its factor of `D_z`-order `> 2` in the light `L²`-weight and
bounds the complementary factor of order `≤ 2` by the `PwBd`-package. -/
theorem ZsummandQPtwise (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (hi : i ≤ 4)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hPf : Work.FTS.H2.HQ.PwBd α f Cf) (hPg : Work.FTS.H2.HQ.PwBd α g Cg) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ Work.FTS.H2.HQ.zsVQ α f g Cf Cg i z θ := by
  intro z hzpos θ hθ0 hθ1
  have hz : z ∈ Iz := le_of_lt hzpos
  -- Leibniz expansion of `D_z^i (f·g)` on the open quadrant
  have hL := Work.FTS.H2.HQ.DzIter_mul_quad i f g hf hg z hz θ ⟨hθ0, hθ1⟩
  have hX : DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (DzIter b f z θ * DzIter (i - b) g z θ)
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2)) := by
    rw [hL, Finset.sum_mul]
  rw [hX, zsVQ_apply α f g Cf Cg i z θ]
  -- the triangle inequality for the finite sum
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun b hb => ?_)
  have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  by_cases hb2 : b ≤ 2
  · -- `b ≤ 2`: `D_z^b f` is the factor pulled out pointwise, `D_z^{i-b} g` is kept
    have hbnd : (DzIter b f z θ) ^ 2 ≤ Cf / (gam α - 1) * HkSq α 4 f := by
      have h := hPf.bound b 0 (by omega) z hzpos θ hθ0 hθ1
      simpa only [Work.Spaces.mixed_zero_right] using h
    have habs : |DzIter b f z θ| ≤ Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f) :=
      Real.abs_le_sqrt hbnd
    rw [zsAAQ_mul_zsFbQ_eq α f g Cf Cg i b z θ hb2]
    calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          simp only [abs_mul]; ring
      _ ≤ (|(i.choose b : ℝ)| * Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f))
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left habs (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(i.choose b : ℝ)| * Real.sqrt (Cf / (gam α - 1) * HkSq α 4 f)
            * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
          rw [abs_mul]
  · -- `2 < b ≤ i ≤ 4`, so `i - b ≤ 2`: now `D_z^{i-b} g` is pulled out pointwise
    have hbnd : (DzIter (i - b) g z θ) ^ 2 ≤ Cg / (gam α - 1) * HkSq α 4 g := by
      have h := hPg.bound (i - b) 0 (by omega) z hzpos θ hθ0 hθ1
      simpa only [Work.Spaces.mixed_zero_right] using h
    have habs : |DzIter (i - b) g z θ| ≤ Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g) :=
      Real.abs_le_sqrt hbnd
    rw [zsAAQ_mul_zsFbQ_eq' α f g Cf Cg i b z θ hb2]
    calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          simp only [abs_mul]; ring
      _ ≤ (|(i.choose b : ℝ)| * |DzIter b f z θ|)
            * (Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g)
              * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right habs (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(i.choose b : ℝ)| * Real.sqrt (Cg / (gam α - 1) * HkSq α 4 g)
            * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
          rw [abs_mul]; ring

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology MeasureTheory
open MeasureTheory Filter Function

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false

/-! ## The iterated `z ∂_z`-identity from a primitive relation -/

/-- If `u = Φ 0` and `Φ j` has derivative `Φ (j+1) z / z` at every `z > 0` (for `j ≤ 2`), then
`DzdIter i u = Φ i` on `(0,∞)` for every `i ≤ 3`.

This is the pointwise half of the main theorem, stated for an abstract pair `(u, Φ)` so that
the induction is independent of `Qang`.  The hypothesis `j ≤ 2` is what makes
`z * ∂_z(Φ j) z = Φ (j+1) z` hold: `DzdIter i u` agrees with `Φ i` on the open half-line, so
their derivatives at `z > 0` agree, and the divided derivative `Φ (j+1) z / z` is undone by the
multiplication by `z`. -/
private theorem DzdIter_eq_of_hasDerivAt {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ 2, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ 3, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
    intro _ z hz
    have hprev : Work.Elliptic.DzdIter i u =ᶠ[𝓝 z] Φ i := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih (by omega) w hw
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
    rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The main identity -/

theorem DzdIter_Qang_ae {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the divided derivative of `Qang g j` for `j ≤ 2` (continuity of `Qang g (j+1)`, `j+1 ≤ 3`)
  have hder2 : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z) (Work.Elliptic.Qang g (j + 1) z / z) z := by
    intro j hj z hz
    exact Work.FTS.H2.hasDerivAt_Qang α g hsm hmem hj hz
      (Work.FTS.H2.continuousOn_Qang α g hsm hmem (by omega))
  -- the pointwise identity for `i ≤ 3`
  have hpoint : ∀ i ≤ 3, ∀ z, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z :=
    DzdIter_eq_of_hasDerivAt (fun z => rfl) hder2
  -- the integrand `x ↦ Qang g 4 x / x` is interval integrable on every compact subinterval of
  -- `(0,∞)`: this is the `j = 3` instance of the Fubini/box integrability
  have hφint : ∀ n : ℕ, IntervalIntegrable (fun x => Work.Elliptic.Qang g 4 x / x) volume
      (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact intervalIntegrable_iff.mpr
      (Work.FTS.H2.QangBoxIntegrable hsm hmem (j := 3) le_rfl ha hab).2
  -- the Lebesgue differentiation theorem on each piece of the countable cover
  have hldt : ∀ᵐ z ∂volume, ∀ n : ℕ, (z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) →
      ∀ c ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        HasDerivAt (fun y => ∫ t in c..y, Work.Elliptic.Qang g 4 t / t)
          (Work.Elliptic.Qang g 4 z / z) z) :=
    MeasureTheory.ae_all_iff.mpr fun n => (hφint n).ae_hasDerivAt_integral
  -- every `z > 0` lies in one of the pieces of the cover
  have hcover : ∀ z : ℝ, 0 < z → ∃ n : ℕ, z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / z) z)
    refine ⟨n, ?_⟩
    have hnz : z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hzn : 1 < z * (n : ℝ) := by
      rw [div_lt_iff₀ hz] at hn1
      linarith
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith, by linarith⟩
  -- `1` lies in every piece of the cover, so the primitive can be taken from `1`
  have h1mem : ∀ n : ℕ, (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
      by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  -- a.e. differentiability of the primitive `y ↦ ∫_1^y Qang g 4 t / t`
  have hprim : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
        (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hldt] with z hz hzpos
    obtain ⟨n, hn⟩ := hcover z hzpos
    exact hz n hn 1 (h1mem n)
  -- hence `Qang g 3` is differentiable a.e. with the divided derivative `Qang g 4 z / z`
  have hderiv3 : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => Work.Elliptic.Qang g 3 y) (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hprim] with z hz hzpos
    have hev : (fun y => Work.Elliptic.Qang g 3 y) =ᶠ[𝓝 z]
        (fun y => (∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
          + Work.Elliptic.Qang g 3 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with y hy
      have h := Work.FTS.H2.Qang_primitive α g hsm hmem (j := 3) (by norm_num) hy
        (by norm_num : (0 : ℝ) < 1)
      linarith
    exact ((hz hzpos).add_const _).congr_of_eventuallyEq hev
  -- the fourth iterate
  have h4 : ∀ᵐ z ∂volume, 0 < z →
      Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g 4 z := by
    filter_upwards [hderiv3] with z hz3 hzpos
    have h3eq : Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Qang g 3 w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with w hw
      exact hpoint 3 le_rfl w hw
    have hd : deriv (Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z)) z
        = Work.Elliptic.Qang g 4 z / z := by
      rw [h3eq.deriv_eq, (hz3 hzpos).deriv]
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd, hd]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hzpos)]
  filter_upwards [h4] with z hz4 hz i hi
  have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · exact hpoint i (by omega) z hz
  · have hieq : i = 4 := by omega
    subst hieq
    exact hz4 hz

end Work.FTS.Nonlinear.N4Fields
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- **The pure `D_z`-slot domination with the full weight.**  For `z > 0` and
`0 < θ < π/2`, the square of the weighted iterate is dominated by the `ℋ⁴`-integrand:

  `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α 4 g z θ`   (`i ≤ 4`).

This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {i : ℕ} (hi : i ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem Qang_sq_w_sq_integral {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`
    have hCS := Work.FTS.H2.Qang_sq_leQ α g hsm hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (Work.FTS.H2.continuousOn_Ktheta_DzIter hsm i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.Nonlinear.N4Fields
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## Monotonicity of the `ℋ^k`-data in `k`

`HkIntegrand α k f` is the sum of the squares of the finitely many weighted derivatives of order
`≤ k` (with the mixed slot switched on for `1 ≤ i ≤ k`), so *increasing* `k` only adds nonnegative
terms: the kernel of this section is the pointwise inequality
`HkIntegrand α k' f z θ ≤ HkIntegrand α k f z θ` for `k' ≤ k`.  The corresponding inequalities for
`HkSq` and `HkNorm` are the reason why an `ℋ⁶`-bound on a solution automatically gives its
`ℋ⁴`-bound, which is what `RegPkgMin.mem4` needs. -/

/-- The two-term `if` comparison behind the monotonicity of the mixed slots. -/
theorem if_le_if_of_imp {a b : Prop} [Decidable a] [Decidable b] (h : a → b) (X : ℝ)
    (hX : 0 ≤ X) : (if a then X else 0) ≤ (if b then X else 0) := by
  by_cases ha : a
  · rw [if_pos ha, if_pos (h ha)]
  · rw [if_neg ha]
    split_ifs with hb
    · exact hX
    · exact le_refl 0

/-- The inner (`j`-)sum of a mixed slot is monotone in the order `k`: the index set grows with `k`
and each summand is switched on for a weaker condition. -/
theorem HkMixedInner_mono (X : ℕ → ℕ → ℝ) (hX : ∀ i j, 0 ≤ X i j) {k k' : ℕ} (hkk : k' ≤ k)
    (i : ℕ) :
    (∑ j ∈ Finset.range (k' + 1), (if 1 ≤ i ∧ i + j ≤ k' then X i j else 0))
      ≤ (∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then X i j else 0)) := by
  refine le_trans (Finset.sum_le_sum (fun j _ => (if_le_if_of_imp (a := 1 ≤ i ∧ i + j ≤ k')
    (b := 1 ≤ i ∧ i + j ≤ k) (fun h => ⟨h.1, le_trans h.2 hkk⟩) (X i j) (hX i j)))) ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.succ_le_succ hkk)) (fun x _ _ => ?_)
  split_ifs with h
  · exact hX i x
  · exact le_refl 0

/-- **Pointwise monotonicity of the `ℋ^k`-integrand in the order**: `k' ≤ k` ⟹
`HkIntegrand α k' f z θ ≤ HkIntegrand α k f z θ`. -/
theorem HkIntegrand_mono (α : ℝ) (f : Fn) {k k' : ℕ} (hkk : k' ≤ k) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k' f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have hrange : Finset.range (k' + 1) ⊆ Finset.range (k + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hkk)
  rw [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg hrange (fun x _ _ => sq_nonneg _)
  · refine le_trans (Finset.sum_le_sum (fun i _ => HkMixedInner_mono
      (fun i j => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (fun i j => sq_nonneg _) hkk i)) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg hrange (fun i _ _ => ?_)
    refine Finset.sum_nonneg (fun j _ => ?_)
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0

/-- **Monotonicity of the `ℋ^k`-square in the order.**  From the `ℋ^k`-membership of `f`
(which makes the outer integrand integrable) and `k' ≤ k`, the order-`k'` norm is bounded by the
order-`k` one. -/
theorem HkSq_mono_of_mem {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkSq α k' f ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hm.2 ?_
  · show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (0 : ℝ) ≤ ∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k' f z θ
    filter_upwards with z
    exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α k' f z θ)
  · show ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k' f z θ)
        ≤ ∫ (θ : ℝ) in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards with z hz
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α k' f z θ))
      (hm.1 z hz) (Filter.Eventually.of_forall (fun θ => HkIntegrand_mono α f hkk z θ))

/-- **Monotonicity of the `ℋ^k`-norm in the order.** -/
theorem HkNorm_mono_of_mem {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkNorm α k' f ≤ Work.Spaces.HkNorm α k f :=
  Real.sqrt_le_sqrt (HkSq_mono_of_mem hkk hm)

/-! ## The `ℋ⁶`-package contains the `ℋ⁴`-one -/

/-- The `ℋ⁶`-bound of `RegPkgH6` gives the uniform `ℋ⁴`-bound used by `RegPkgGal`
(design §4), as soon as the `ℋ⁶`-membership needed by `HkNorm_mono_of_mem` is available. -/
theorem RegPkgH6.bd4 {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) :
    ∃ C, ∀ τ, 0 ≤ τ → τ ≤ T → Xn4 α (slice g τ) ≤ C := by
  obtain ⟨C, hC⟩ := h.bd6
  refine ⟨C, fun τ hτ hτT => ?_⟩
  have hm := h.mem6 τ hτ hτT
  exact le_trans (HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hm) (hC τ hτ hτT)

/-- The `ℋ⁴`-membership clause of `RegPkgH6`, through the `ℋ⁴`-field of its `RegPkgMin` (no
monotonicity of `ℋ^k`-membership in the order is needed for this clause: it is a field of the
package). -/
theorem RegPkgH6.mem4 {α T : ℝ} {g : Fam} (h : RegPkgH6 α T g) {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.Spaces.HkMem α 4 (slice g τ) := h.min.mem4 τ hτ

/-! ## `SmoothOpen` and `SmoothQuad` against the consumers

The strong route states its regularity in the *finite* order `4` (`RegPkgMin.c4`), while the frozen
frozen classes are stated with `smoothOrder` (`SmoothOpen`, `SmoothQuad`) or with `HQo`.  The two
directions used below are `SmoothOpen ⟹ C⁴` (the order-`4` clause of a smooth object) and
`SmoothQuad ⟹ SmoothOpen` (so that `RegQ` feeds the estimates that are stated on `HQo`). -/

/-- `SmoothOpen` means `C^∞` on the open quadrant, hence in particular `C⁴`. -/
theorem SmoothOpen.contDiffOn_four {f : Fn} (h : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
  h.of_le (by simp [Work.Stability.smoothOrder])



end Work.FTS.StrongLWP
end
end
-- ===== merged: Submission.Work.FTS.TransportS.GalSide =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `DecayAll` is monotone in the order -/





end Work.FTS.TransportS
end
end
