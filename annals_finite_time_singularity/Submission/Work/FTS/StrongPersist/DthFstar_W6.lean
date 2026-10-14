import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.CoercivityStep.Step.HkIPStep_core
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.LWP.Main
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.ConstructionInstance.Tie =====
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

/-! ## The reconstructed velocity of the ansatz -/

/-- **The velocity of the self-similar ansatz**: `u(x,t) = BS(ω(·,t)) x`, the Biot–Savart
reconstruction of the constructed vorticity `solVort P`. -/
def ansatzV {α : NNReal} (P : ProfileData α) : R3 → ℝ → R3 :=
  fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x




/-- **The datum identity for the velocity** (finding G): with the normalisation `λ̄(0) = 1`, the
ansatz velocity at `t = 0` is the Biot–Savart field of the `St1` cut-off datum
`ω₀ = χ(ρ/L)·omegaS p g` — this is the `init` field of `IsLocalEulerEquationSolution` for the
candidate solution. -/
theorem ansatzV_zero {α : NNReal} (P : ProfileData α) :
    (ansatzV P · 0) = Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L) := by
  funext x
  change Work.LWP.biotSavart (fun y => solVort P y 0) x
      = Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L) x
  rw [show (fun y => solVort P y 0) = omega₀ (profExp α) P.g P.L from
    funext (fun y => solVort_zero_eq_cutDatum P y)]

/-- **The Biot–Savart law for the ansatz**: the vorticity of the reconstructed velocity is the
constructed vorticity (`Work.SolutionDelivery`'s dictionary clause). -/
theorem vorticity_ansatzV {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ preWindow P.T, ∀ x : R3,
      vorticity (fun y => ansatzV P y t) x = solVort P x t :=
  fun t ht x => vorticity_biotSavart_solVort P hlaw t ht x

/-- **Divergence-freeness of the ansatz velocity**, from the Biot–Savart law and the
divergence-freeness of the constructed vorticity (`Reduced.solVort_div`). -/
theorem div_ansatzV {α : NNReal} (P : ProfileData α) (hlaw : Work.LWP.BiotSavartLaw) :
    ∀ t ∈ preWindow P.T, div (fun x => ansatzV P x t) = 0 := by
  intro t ht
  funext x
  exact (hlaw (fun y => solVort P y t) (solVort_integrable P t ht)
    (solVort_isBoundedFun P t ht) (fun y => congrFun (solVort_div P t ht) y)).2 x

/-- **Oddness of the ansatz velocity** (the `Cyl` parity dictionary, via
`isOdd_biotSavart_solVort`). -/
theorem odd_ansatzV {α : NNReal} (P : ProfileData α) :
    ∀ t ∈ Set.Ico 0 P.T, IsOdd (ansatzV P · t) :=
  fun t ht => isOdd_biotSavart_solVort P t ⟨by linarith [ht.1], ht.2⟩

/-! ## The named residuals -/

/-- **Residual 3 (`smooth`)**: the ansatz velocity is `C¹` on the *two-sided* open window
`preWindow T = (-2, T)`.  This is the construction's backward extension of the solution (the
field `smooth` of the delivered interface); the LWP chapter delivers the forward strips only. -/
def SelfSimVortSmooth {α : NNReal} (P : ProfileData α) : Prop :=
  ContDiffOn ℝ 1 (ansatzV P).uncurry (Set.univ ×ˢ preWindow P.T)

/-- **Residual 4 (`maximal`)**: the blow-up time `T` is *maximal*, i.e. the ansatz cannot be
extended past `T` as a solution of the Euler equation with the same datum.  This is exactly the
`maximal` field of `Work.LWP.MaximalSolution` for the candidate solution `ansatzV P`.

The quantitative half of this statement is a theorem of this directory: `St5` (the field
`hansatz` of `ProfileData`, `Reduced.solVort_hansatz`) forces the vorticity sup-norm to grow like
`c/(T-t)`, hence `bkm (ansatzV P) t ⟶ ∞` as `t → T⁻`; the remaining half is the Beale–Kato–Majda
continuation input `Work.LWP.LWPInputs.bkm` (see `NOTES.md` §3.5). -/
def SelfSimMaximal {α : NNReal} (P : ProfileData α) : Prop :=
  ¬ ∃ T' : ℝ, P.T < T' ∧ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
    IsLocalEulerEquationSolution p' (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) T' u' ∧
    Work.LWP.ExtendsField (ansatzV P) u' P.T

/-- **Residual 2 is the LWP chapter's own notion**: `SelfSimLGClass` is *definitionally*
`Work.LWP.SpaceTimeHolder` for the ansatz velocity.  (The residual therefore needs no new
vocabulary: it is the analytic class the LWP owner must supply.) -/
theorem selfSimLGClass_iff_spaceTimeHolder {α : NNReal} (P : ProfileData α) :
    SelfSimLGClass α P ↔ Work.LWP.SpaceTimeHolder α (ansatzV P) P.T := Iff.rfl

/-! ## The reduction of `tie` -/

/-- **THE REDUCTION**: `tie` follows from the four named residuals and the LWP inputs.

The candidate solution is `u = ansatzV P = BS(solVort P · )`, with pressure reconstructed from the
vorticity equation; every field of `Work.LWP.MaximalSolution` is then supplied:

* `T_pos`, `p`, `u`, `maximal` — the hypotheses (`P.hT`, `LWPInputs.pressure`, `SelfSimMaximal`);
* `sol` — `solContDiff` from `SelfSimVortSmooth` (the open window contains `Ico 0 T`),
  `pressureContDiff`/`eq` from the reconstruction, `div_free` from the Biot–Savart law,
  `init` from the datum identity `ansatzV_zero`;
* `odd` — `odd_ansatzV`;
* `spacetime` — `SelfSimLGClass` (residual 2). -/
theorem selfSimilarEulerSolution_of {α : NNReal} (P : ProfileData α)
    (hlwp : Work.LWP.LWPInputs α)
    (hv : SelfSimVorticityEquation α P)
    (hG : SelfSimLGClass α P)
    (hsm : SelfSimVortSmooth P)
    (hmax : SelfSimMaximal P) :
    SelfSimilarEulerSolution α P.T P := by
  -- the pressure: the vorticity equation plus the spacetime class give the Euler equation
  have hvt : ∀ t ∈ Set.Ico 0 P.T, ∀ x : R3,
      vorticity (fun y => ansatzV P y t) x = solVort P x t :=
    fun t ht x => vorticity_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩ x
  have hdiv : ∀ t ∈ Set.Ico 0 P.T, div (fun x => ansatzV P x t) = 0 :=
    fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨p, hpc, hpe⟩ := hlwp.pressure (ansatzV P) (solVort P) P.T
    ((selfSimLGClass_iff_spaceTimeHolder P).mp hG) hvt hdiv hv
  refine ⟨{ T_pos := P.hT
            p := p
            u := ansatzV P
            sol := { solContDiff := hsm.mono (fun q hq =>
                        ⟨trivial, ⟨by linarith [hq.2.1], hq.2.2⟩⟩)
                     pressureContDiff := hpc
                     eq := hpe
                     div_free := fun t ht => hdiv t ⟨le_of_lt ht.1, ht.2⟩
                     init := ansatzV_zero P }
            odd := odd_ansatzV P
            spacetime := (selfSimLGClass_iff_spaceTimeHolder P).mp hG
            maximal := hmax }, ?_, hsm⟩
  intro t ht x
  rfl

/-! ## The residual interface, and the instantiation from it -/

/-- **The residual interface of the construction, with every field named.**
`TieInputs α P` consists of the LWP chapter's analytic inputs (whose own residual list is
`Work.LWP.NOTES.md`) and the four analytic outputs of the sibling chapters listed at the top of
this file.  Nothing else: the profile/modulation data `P : ProfileData α` is *inhabited*
(`profileData_inhabited`), and every field about the vorticity is a theorem (`Reduced`). -/
structure TieInputs (α : NNReal) (P : ProfileData α) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- **residual 1**: the ℝ³ vorticity equation for `u = BS ω` (`Work.Stability`'s bootstrap) -/
  vortEq : SelfSimVorticityEquation α P
  /-- **residual 2**: the spacetime Lichtenstein–Gunther class of `BS(ω(·,t))` (`Work.LWP`) -/
  lgClass : SelfSimLGClass α P
  /-- **residual 3**: `C¹` of the ansatz velocity on the two-sided window (backward extension) -/
  smooth : SelfSimVortSmooth P
  /-- **residual 4**: maximality of `T` (`St5` + Beale–Kato–Majda) -/
  maximal : SelfSimMaximal P
  /-- **residual 5 (finding H)**: the time-Hölder regularity of `∂ₜω` on the strips, consumed by
  the far-field step of the `St4` assembly -/
  timeHolderDeriv : SelfSimTimeHolderDeriv P

/-- **`tie` from the residual interface.** -/
theorem tie_of_tieInputs {α : NNReal} {P : ProfileData α} (T : TieInputs α P) :
    SelfSimilarEulerSolution α P.T P :=
  selfSimilarEulerSolution_of P T.lwp T.vortEq T.lgClass T.smooth T.maximal

/-- **The instantiation**: the residual interface `TieInputs` produces the repaired input package
`Patch.ConstructionDataFixed` (and hence, through `Patch.constructedSolutionFixed`, the whole
constructed-solution package). -/
def constructionDataFixed_of_tieInputs {α : NNReal} {P : ProfileData α} (T : TieInputs α P) :
    ConstructionDataFixed α :=
  { lwp := T.lwp
    prof := P
    tie := tie_of_tieInputs T
    hThDt := T.timeHolderDeriv }

/-- **The instantiation, at the level of the constructed solution.** -/
def constructedSolutionFixed_of_tieInputs {α : NNReal} {P : ProfileData α}
    (T : TieInputs α P) : ConstructedSolutionFixed α :=
  constructedSolutionFixed (constructionDataFixed_of_tieInputs T)

/-! ## Finding (H): the object behind the `∂ₜω`-time-Hölder residual -/

/-- **What residual 5 really is: a bound on `∂ₜ²ω`.**

The mean value theorem (`timeHolderOnBall_of_timeDeriv_le`, applied to the field `∂ₜω`) turns a
bound on the *second* time derivative of `ω` into the time-Hölder regularity of `∂ₜω`.  This pins
the exact analytic object the `St4` far-field step needs from the construction: not the `C^{1,α}`
class of `ω` (which is false, finding A), but `λ̄³‖∂ₜ²ω‖ ≤ M₂` on the window — which for the
explicit self-similar field is a finite computation in the profile data (it requires the second
`z`-derivative of the profile and the second derivative of `λ̄`, neither of which is currently a
field of `ProfileData`; see `NOTES.md` §3.5). -/
theorem timeHolderOnBall_timeDeriv_of_secondDeriv {α Λ R S : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hΛ : 0 ≤ Λ) {ω : R3 → ℝ → R3}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Work.StabilityFar.window S,
      HasDerivAt (fun t => FiniteTimeSingularity.timeDeriv ω z t)
        (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) z s) s)
    (hbd : ∀ z ∈ Metric.closedBall (0 : R3) R, ∀ s ∈ Work.StabilityFar.window S,
      ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv ω) z s‖ ≤ Λ) :
    ∃ H : ℝ, 0 ≤ H ∧ Work.StabilityFar.TimeHolderOnBall α
      (FiniteTimeSingularity.timeDeriv ω) R S H :=
  timeHolderOnBall_of_timeDeriv_le (α := α) (Λ := Λ) (R := R) (S := S)
    (ω := FiniteTimeSingularity.timeDeriv ω) hα0 hα1 hΛ hdiff hbd


/-! ## Finding (I): the blow-up form of the maximality residual, and the reduction to it -/

/-- **Finding (I)**: the `maximal` field of `Work.LWP.MaximalSolution` forbids extensions of class
`C¹` only (no bound on the vorticity, no decay), against which the Beale–Kato–Majda criterion is
powerless.  The honest form of the maximality of `T` is the *blow-up* statement: the cut-off datum
`BS ω₀` admits no maximal solution living past `P.T`. -/
def SelfSimBlowUp {α : NNReal} (P : ProfileData α) : Prop :=
  ∀ T' : ℝ, P.T < T' →
    ¬ Nonempty (Work.LWP.MaximalSolution α
      (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) T')

/-- **Restriction of an Euler solution to a smaller time horizon.** -/
theorem isLocalEulerEquationSolution_mono {p : R3 → ℝ → ℝ} {u₀ : R3 → R3} {T T' : ℝ}
    {u : R3 → ℝ → R3} (h : IsLocalEulerEquationSolution p u₀ T u) (hT : T' ≤ T) :
    IsLocalEulerEquationSolution p u₀ T' u where
  solContDiff :=
    h.solContDiff.mono (fun q hq => ⟨trivial, ⟨hq.2.1, lt_of_lt_of_le hq.2.2 hT⟩⟩)
  pressureContDiff :=
    h.pressureContDiff.mono (fun q hq => ⟨trivial, ⟨hq.2.1, lt_of_lt_of_le hq.2.2 hT⟩⟩)
  eq := fun x t ht => h.eq x t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  div_free := fun t ht => h.div_free t ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩
  init := h.init

/-- **The Lichtenstein–Gunther datum classes of the cut-off datum, from the profile data alone.**
This is certificate 2 of the patch applied to `ProfileData`: the measurability, the `L^∞` bound,
the `α`-Hölder regularity, the divergence-freeness and the parity of
`ωS = omegaS (profExp α) P.g` are all theorems of this directory
(`aestronglyMeasurable_omegaS`, `omegaS_norm_le`, `holder_omegaS_of_data`, `div_omega0_all`,
`isOddVorticity_omegaS` + `isAxiNoSwirl_omega₀` + `isOdd_biotSavart_of_axiNoSwirl`). -/
theorem datumData_of_profile {α : NNReal} (P : ProfileData α) (hlwp : Work.LWP.LWPInputs α) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) ∧
      Work.LWP.EulerDataBS α (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) := by
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  refine datumData_of_cut_of_holder hlwp P.hL P.hM P.hα hα1
    (aestronglyMeasurable_omegaS P.hmeasP)
    (fun x => omegaS_norm_le hp hp1 (bdd_g P) P.hCg (fun θ hθ => by
      have hG : Gamma (profExp α / 3) θ ≤ 1 :=
        Gamma_le_one (by rw [profExp]; positivity) hθ
      have hG0 : 0 ≤ Gamma (profExp α / 3) θ := Gamma_nonneg hθ
      have hp0 : 0 ≤ profExp α := profExp_nonneg α
      nlinarith [P.hMprof, hG, hG0, hp0]) x)
    (holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ P.hvt P.hquad0 P.hquad P.hvan P.hzk
      P.hzth (P.hsmooth.of_le le_top))
    (div_omega0_all hp hp1 P.hvt (Work.Stability.SmoothFar.of_smoothNbhd P.hsmooth) P.L)
    (Work.SolutionDelivery.isOdd_biotSavart_of_axiNoSwirl
      (isOddVorticity_cutDatum (isOddVorticity_omegaS (by rw [profExp]; positivity) P.hvt))
      (isAxiNoSwirl_omega₀ (profExp α) P.g P.L))

/-- **Finding (I), the reduction**: the maximality residual follows from the *blow-up* statement.

Let `hm` be a maximal solution of the datum `BS ω₀` (which exists by `LWPInputs.maxExists` applied
to the datum clauses `datumData_of_profile`).  If an extension `u'` of the ansatz to `[0,T')`,
`T' > P.T`, existed, then (i) for `T_max ≤ P.T` the ansatz agrees with `hm.u` on `[0,T_max)` by
`LWPInputs.uniqueness` (both are LG-class solutions with the same datum `BS ω₀`), so `u'` extends
`hm` past `T_max`, contradicting `hm.maximal`; (ii) for `P.T < T_max` the existence of `hm`
contradicts the blow-up hypothesis. -/
theorem selfSimMaximal_of_blowUp {α : NNReal} (P : ProfileData α)
    (hlwp : Work.LWP.LWPInputs α) (hv : SelfSimVorticityEquation α P)
    (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P) (h : SelfSimBlowUp P) :
    SelfSimMaximal P := by
  -- the ansatz is an Euler solution with the cut-off datum
  obtain ⟨p, hpcd, hpe⟩ := hlwp.pressure (ansatzV P) (solVort P) P.T
    ((selfSimLGClass_iff_spaceTimeHolder P).mp hG)
    (fun t ht x => vorticity_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩ x)
    (fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩) hv
  have hsol : IsLocalEulerEquationSolution p
      (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) P.T (ansatzV P) :=
    { solContDiff := hsm.mono (fun q hq => ⟨trivial, ⟨by linarith [hq.2.1], hq.2.2⟩⟩)
      pressureContDiff := hpcd
      eq := hpe
      div_free := fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩
      init := ansatzV_zero P }
  -- a maximal solution of the datum exists
  obtain ⟨hdat, hdatBS⟩ := datumData_of_profile P hlwp
  obtain ⟨Tmax, hpos, hne⟩ := hlwp.maxExists _ hdat hdatBS
  obtain ⟨hm⟩ := hne
  rintro ⟨T', hT', p', u', hu', hext⟩
  rcases le_or_gt Tmax P.T with hle | hlt
  · -- `hm` and the ansatz agree on `[0,Tmax)`, so `u'` extends `hm` past `Tmax`
    have huniq : ∀ x t, t ∈ Set.Ico 0 Tmax → hm.u x t = ansatzV P x t :=
      hlwp.uniqueness _ Tmax hm.p p hm.u (ansatzV P) hm.sol
        (isLocalEulerEquationSolution_mono hsol hle)
        (fun S hS => hm.spacetime S hS)
        (fun S hS => hG S ⟨hS.1, lt_of_lt_of_le hS.2 hle⟩)
    exact hm.maximal ⟨T', lt_of_le_of_lt hle hT', p', u', hu', fun x t ht =>
      (hext x t ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩).trans (huniq x t ht).symm⟩
  · exact h Tmax hlt ⟨hm⟩

/-- **The blow-up statement in the LWP chapter's own vocabulary**: the cut-off datum `BS ω₀`
admits no Lichtenstein–Gunther solution (`Work.LWP.LGClass`: the Euler solution together with the
oddness and the joint `C^{1,α}` class on every strip) past `P.T`.  This is the form of the
maximality statement that the `St1`–`St5` a priori estimates prove. -/
def SelfSimNoLG {α : NNReal} (P : ProfileData α) : Prop :=
  ∀ T' : ℝ, P.T < T' → ¬ ∃ p' : R3 → ℝ → ℝ, ∃ u' : R3 → ℝ → R3,
    Work.LWP.LGClass α (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) T' p' u'

/-- **`SelfSimNoLG` implies `SelfSimBlowUp`**: a maximal solution at `T' > P.T` is in particular an
LG-class solution of the datum on `[0,T')`, contradicting the blow-up statement. -/
theorem selfSimBlowUp_of_noLG {α : NNReal} (P : ProfileData α) (h : SelfSimNoLG P) :
    SelfSimBlowUp P := by
  rintro T' hT' ⟨hm⟩
  exact h T' hT' ⟨hm.p, hm.u, ⟨hm.sol, hm.odd, hm.spacetime⟩⟩

/-- **`tie` from the blow-up form of maximality**: the composition of
`selfSimMaximal_of_blowUp` with the decomposition `selfSimilarEulerSolution_of`. -/
theorem selfSimilarEulerSolution_of_blowUp {α : NNReal} (P : ProfileData α)
    (hlwp : Work.LWP.LWPInputs α) (hv : SelfSimVorticityEquation α P)
    (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P) (h : SelfSimBlowUp P) :
    SelfSimilarEulerSolution α P.T P :=
  selfSimilarEulerSolution_of P hlwp hv hG hsm
    (selfSimMaximal_of_blowUp P hlwp hv hG hsm h)

/-- **The residual interface in the paper's own form**: the same four analytic inputs as
`TieInputs`, with the maximality residual replaced by the blow-up statement
(`SelfSimBlowUp P`, finding I). -/
structure TieInputsBlowUp (α : NNReal) (P : ProfileData α) where
  /-- the LWP chapter's analytic inputs -/
  lwp : Work.LWP.LWPInputs α
  /-- **residual 1**: the ℝ³ vorticity equation (`Work.Stability`'s bootstrap) -/
  vortEq : SelfSimVorticityEquation α P
  /-- **residual 2**: the spacetime Lichtenstein–Gunther class of `BS(ω(·,t))` (`Work.LWP`) -/
  lgClass : SelfSimLGClass α P
  /-- **residual 3**: `C¹` of the ansatz velocity on the two-sided window (backward extension) -/
  smooth : SelfSimVortSmooth P
  /-- **residual 4'**: the datum blows up at `P.T` (`St1`–`St5` + BKM) -/
  blowUp : SelfSimBlowUp P
  /-- **residual 5 (finding H)**: the time-Hölder regularity of `∂ₜω` on the strips -/
  timeHolderDeriv : SelfSimTimeHolderDeriv P

/-- **The instantiation from the blow-up interface.** -/
def constructionDataFixed_of_blowUpInputs {α : NNReal} {P : ProfileData α}
    (T : TieInputsBlowUp α P) : ConstructionDataFixed α :=
  { lwp := T.lwp
    prof := P
    tie := selfSimilarEulerSolution_of_blowUp P T.lwp T.vortEq T.lgClass T.smooth T.blowUp
    hThDt := T.timeHolderDeriv }

/-! ## Certificates -/

/-- **Certificate A — the decomposition of `tie` elaborates**: from the residual interface, the
repaired residual package. -/
example {α : NNReal} {P : ProfileData α} (T : TieInputs α P) : ConstructionDataFixed α :=
  constructionDataFixed_of_tieInputs T

/-- **Certificate B — the whole constructed-solution package follows.** -/
example {α : NNReal} {P : ProfileData α} (T : TieInputs α P) : ConstructedSolutionFixed α :=
  constructedSolutionFixed_of_tieInputs T

/-- **Certificate C — the residual list is *closed* under the derivations of this directory**:
every vorticity-level field of the repaired package is a theorem about `solVort`, for any
`TieInputs` at all. -/
example {α : NNReal} {P : ProfileData α} (T : TieInputs α P) :
    (∀ t : ℝ, ∀ y : R3, solVort P y t ≠ 0 → y ∈ Metric.closedBall 0 P.R) ∧
      (∀ t ∈ preWindow P.T, ∀ y : R3, P.lam t * ‖solVort P y t‖ ≤ P.M) ∧
        (∀ t ∈ Set.Ico 0 P.T, ∃ x : R3,
          c₀star α * (α : ℝ) ≤ P.lam t * ‖solVort P x t‖) ∧
          (∀ t ∈ preWindow P.T, FiniteTimeSingularity.div (solVort P · t) = 0) :=
  ⟨fun t y hy => solVort_supp P t y hy, solVort_bdd P, solVort_hansatz P, solVort_div P⟩

/-- **Certificate D — the datum clauses are a theorem of `ProfileData`** (no `holder` field of
`ProfileData` is needed beyond the uniform moduli): for every `P : ProfileData α` and every LWP
input bundle, the cut-off datum of `P` is Lichtenstein–Gunther admissible. -/
example {α : NNReal} (P : ProfileData α) (hlwp : Work.LWP.LWPInputs α) :
    Work.LWP.EulerData α (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) ∧
      Work.LWP.EulerDataBS α (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) :=
  datumData_of_profile P hlwp

/-- **Certificate E — the maximality residual follows from the blow-up statement** (finding I). -/
example {α : NNReal} (P : ProfileData α) (hlwp : Work.LWP.LWPInputs α)
    (hv : SelfSimVorticityEquation α P) (hG : SelfSimLGClass α P) (hsm : SelfSimVortSmooth P)
    (h : SelfSimBlowUp P) : SelfSimMaximal P :=
  selfSimMaximal_of_blowUp P hlwp hv hG hsm h

/-- **Certificate F — the paper's-form residual interface produces the patched package.** -/
example {α : NNReal} {P : ProfileData α} (T : TieInputsBlowUp α P) : ConstructionDataFixed α :=
  constructionDataFixed_of_blowUpInputs T

/-- **Certificate G — the paper's-form residual interface produces `tie`.** -/
example {α : NNReal} {P : ProfileData α} (T : TieInputsBlowUp α P) :
    SelfSimilarEulerSolution α P.T P :=
  selfSimilarEulerSolution_of_blowUp P T.lwp T.vortEq T.lgClass T.smooth T.blowUp

/-- **Certificate H — the maximality residual in LWP's own vocabulary implies the blow-up form.** -/
example {α : NNReal} (P : ProfileData α) (h : SelfSimNoLG P) : SelfSimBlowUp P :=
  selfSimBlowUp_of_noLG P h

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert.galFun_adm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false

/-! ## Scalar homogeneity of the mixed derivatives

The iterated operators `D_z`, `D_θ` and their mixed iterates commute with multiplication by a
constant **unconditionally**: `deriv` is scalar homogeneous with no differentiability hypothesis
(if `f` is not differentiable at `x` then neither is `c · f` for `c ≠ 0`, and both sides vanish).
This is the same argument as the `private` lemmas of
`Submission/Work/FTS/Galerkin/Hilbert/HkMem_const_mul.lean`, restated here because they are not
exported. -/










/-! ## Smoothness of finite linear combinations

`SmoothNbhd` is closed under finite linear combinations with arbitrary real coefficients: it is
closed under addition (`Work.FTS.CoercivityStep.Step.SmoothNbhd_add`) and under multiplication by
a constant (`Work.FTS.CoercivityStep.Step.SmoothNbhd_const_mul`). -/


/-! ## `ℋ^k`-membership of finite linear combinations -/


/-! ## Linearity of the mixed operator over finite combinations -/


/-! ## Congruence of the `L₁₂` zero mode -/


/-! ## Additivity of the `L₁₂` zero mode -/



/-! ## The main theorem

The proof assembled below follows the route of the docstring, with these local ingredients:

* `SmoothNbhd_finsetSum` — `SmoothNbhd` is closed under finite linear combinations;
* `HkMem_finsetSum` — `ℋ^k` is closed under finite linear combinations (induction on the finset
  from `Work.FTS.Galerkin.Hilbert.HkMem_add` and `HkMem_const_mul`);
* `mixed_finsetSum` — the mixed operator is linear over a finite combination of `SmoothNbhd`
  functions, pointwise on `Work.Spaces.nbhU` (hence on the closed quadrant);
* `L12f_congr` — the `L₁₂` zero mode is a congruent integral, so it only sees `(0,∞) × Iθ`;
* `L12f_add_of_smooth` and `L12f_finsetSum_zero` — the `L₁₂` zero mode is additive over finite
  combinations of functions vanishing individually, the integrability inputs coming from the
  `HkMem` clauses through `Work.Coercivity.L12dens_integrableOn`.

The only transfer that is not purely formal is the passage from the explicit finite combination
`∑ k, c k * mixed b a (φ k)` (about which `HkMem_finsetSum`/`L12f_finsetSum_zero` speak) to the
literal mixed derivative `mixed b a (galFun φ c)` of the Galerkin profile: this uses
`mixed_finsetSum` pointwise on the neighbourhood together with
`Work.Coercivity.HkMem_congr_Ioi` (resp. `L12f_congr`). -/


end Work.FTS.Galerkin.Hilbert
end
end
-- ===== merged: Submission.Work.FTS.H2.HQ.ZsummandQ =====
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

/-- **The pure `D_z`-summand of the interior product rule `HProdQ`.**

For `f, g` in the interior class `Work.FTS.Nonlin.RegQ α 4` (`= SmoothQuad ∧ HkMem α 4 ∧
BdryTraces α 4`) and pointwise `L^∞`-bound packages `PwBd α f Cf`, `PwBd α g Cg`
(Corollary `SecondDerivativesBounded` for the interior class, see `HQ/Glue.lean`), the pure
`D_z`-slots of the `ℋ⁴`-integrand of the product `f·g` are square integrable, with
`L2Sq (D_z^i (f g) · w/sin(2θ)^{η/2}) ≤ C/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}` for `i ≤ 4`.

This is `Work.Spaces.HProductRule_Zsummand` (proved) with the *unusable* class
`Spaces.SmoothNbhd` (analyticity on a neighbourhood of the closed quadrant) replaced by
`RegQ` and with the pointwise `L^∞`-bound of order `≤ 2` supplied abstractly by `PwBd`
(instead of `Work.Spaces.MixedSqPointwiseBound`).  Route: copy the proof of
`Submission/Work/Spaces/HProductRule_Zsummand.lean`, using
* `Work.FTS.H2.HQ.DzIter_mul_quad` (the `D_z`-Leibniz rule for `SmoothQuad`, in `HQ/Glue.lean`)
  in place of `Work.Spaces.DzIter_mul`;
* `Work.FTS.H2.HQ.L2Mem_light_quad`, `Work.FTS.H2.HQ.aesm_light_prod`,
  `Work.FTS.H2.HQ.aesm_light_slice` (in `HQ/Glue.lean`) in place of the corresponding
  `Work.Spaces.HPRZ` lemmas (which need `SmoothNbhd`); note that the latter must be applied to
  `f`, to `g` and to the product `f·g` only through `SmoothQuad` (the `HkMem` hypothesis is not
  available for the product — that is what is being proved), so use
  `Work.FTS.H2.HQ.aesm_light_prod/slice` for the product and `LocData.smoothQuad_mul`;
* the `PwBd` hypothesis for the factor of order `≤ 2` (its `bound` field is stated on the open
  quadrant, `PwBd.nonneg` for nonnegativity);
* the pure lemmas `L2Sq_DzIter_le_HkSq`, `sq_le_HkIntegrand_z` and the `Work.Spaces.HPRZ`
  toolkit for the `L²`-bookkeeping.
Trap: `RegQ` constrains nothing on `θ = 0, π/2` and (for the `PwBd` bound) nothing at `z = 0`,
so all the pointwise estimates must be taken where the weights do not vanish: on
`z = 0` and on `sin(2θ) = 0` both sides of every pointwise inequality used here vanish (the
weights `w z` and `wTheta α θ` are `0` there), and the *integrals* are blind to those lines
(`ae_restrict_mem measurableSet_Ioo`, `MeasureTheory.Ioo_ae_eq_Icc`). -/
theorem ZsummandQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn)
    (Cf Cg : ℝ), 0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg → ∀ i ≤ 4,
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ C / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g Cf Cg hα hα1 hregf hregg hPf hPg i hi
  obtain ⟨hf, hmf, -⟩ := hregf
  obtain ⟨hg, hmg, -⟩ := hregg
  have hγ : 0 < gam α - 1 := gam_sub_one_pos hα
  -- the product of two `SmoothQuad` functions is `SmoothQuad`
  have hfg : SmoothQuad (fun z θ => f z θ * g z θ) :=
    Work.FTS.LocData.smoothQuad_mul hf hg
  -- the `L²`-bookkeeping of the majorant, and the interior pointwise majorant
  have hV := ZsummandQL2 α f g Cf Cg hγ hPf.nonneg hPg.nonneg i hi hf hg hmf hmg
  have hint := ZsummandQPtwise α f g Cf Cg i hi hf hg hPf hPg
  -- ## Step 1: the pointwise domination of the slot by the majorant, on the *closed* quadrant.
  -- On the two degenerate lines the light weight vanishes, and the majorant is nonnegative.
  have hdom : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| ≤ |zsVQ α f g Cf Cg i z θ| := by
    intro z hz θ hθ
    have hUnn : 0 ≤ zsVQ α f g Cf Cg i z θ := zsVQ_nonneg α f g Cf Cg i z θ
    rw [abs_of_nonneg hUnn]
    rcases lt_or_eq_of_le (Set.mem_Ici.mp hz) with hzpos | hz0
    · rcases lt_or_eq_of_le (Set.mem_Icc.mp hθ).1 with hθpos | hθzero
      · rcases lt_or_eq_of_le (Set.mem_Icc.mp hθ).2 with hθlt | hθpi
        · exact hint z hzpos θ hθpos hθlt
        · have hsin : Real.sin (2 * θ) = 0 := by
            rw [hθpi, show 2 * (π / 2) = π by ring, Real.sin_pi]
          rw [light_eq_zero_of_sin hsin, mul_zero, abs_zero]
          exact hUnn
      · have hsin : Real.sin (2 * θ) = 0 := by rw [← hθzero]; simp
        rw [light_eq_zero_of_sin hsin, mul_zero, abs_zero]
        exact hUnn
    · subst hz0
      rw [light_eq_zero_of_z, mul_zero, abs_zero]
      exact hUnn
  -- ## Step 2: the slot is `L2Mem`, by domination by the (measurable) majorant
  have hFs : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) (volume.restrict Iθ) :=
    fun z hz => (aesm_light_slice (fun z θ => f z θ * g z θ) hfg i hz).pow 2
  have hFo : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) :=
    ((aesm_light_prod (fun z θ => f z θ * g z θ) hfg i).pow 2).integral_prod_right'
  have hmem : L2Mem (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) :=
    Work.Spaces.HPRZ.L2Mem_of_abs_le (F := fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) (U := zsVQ α f g Cf Cg i)
      hV.1 hFs hFo hdom
  -- ## Step 3: the squared `L²`-bound
  have hL2 : L2Sq (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ≤ L2Sq (zsVQ α f g Cf Cg i) := by
    rw [L2Sq, L2Sq]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hV.1.2 ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _)) (hV.1.1 z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    have h := pow_le_pow_left₀ (abs_nonneg _) (hdom z hz θ hθ) 2
    simpa only [sq_abs] using h
  exact ⟨hmem, le_trans hL2 hV.2⟩

end Work.FTS.H2.HQ
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `α^{-3/2}X³ ≤ Pbd α X`. -/
theorem rpow_neg_three_half_mul_cube_le_Pbd {α X : ℝ} (hα : 0 < α) (hX : 0 ≤ X) :
    α ^ (-(3 / 2 : ℝ)) * X ^ 3 ≤ Pbd α X := by
  rw [Pbd]
  have h1 : (0 : ℝ) ≤ α ^ 2 * X := mul_nonneg (by positivity) hX
  have h2 : (0 : ℝ) ≤ Real.sqrt α * X ^ 2 := mul_nonneg (Real.sqrt_nonneg α) (by positivity)
  have h3 : (0 : ℝ) ≤ α ^ (-(5 / 2 : ℝ)) * X ^ 4 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (by positivity)
  linarith


end Work.FTS.Nonlin
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.Fstar_pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The sharp radial bound for the iterated derivatives of `h(z) = z/(1+z)²` -/



/-! ## The weighted angular bound for the `D_θ`-iterates of `Γ` -/


/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_zpow_deriv_Hz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open scoped Topology

/-! ## Elementary ingredients

`Hz z = 2z(1-z)/(1+z)³` is the radial factor of `D_z F_*`.  The route to the weighted bound
`|z^n Hz^{(n)}(z)| ≤ C·z/(1+z)²` is the closed form for the iterated derivatives
(`iter_deriv_Hz`) together with the weighted bound for the closed form `hKerClosed` of the
derivatives of `h(z) = z/(1+z)²` (`zpow_hKerClosed_le`). -/

/-- The absolute value of the closed form `hKerClosed k z = (-1)^k k! (z-k)(1+z)^{-(k+2)}`. -/
private lemma abs_hKerClosed (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |Work.Spaces.hKerClosed k z|
      = (k.factorial : ℝ) * |z - (k : ℝ)| * ((1 + z)⁻¹) ^ (k + 2) := by
  have h1 : (0:ℝ) < 1 + z := by linarith
  unfold Work.Spaces.hKerClosed
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ)),
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt h1)) _), abs_pow]
  norm_num
  ring

/-- The elementary inequality `|z^k (z-k)| ≤ (k+1) z (1+z)^k` for `z ≥ 0`. -/
private lemma zpow_mul_sub_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * (z - (k : ℝ))| ≤ ((k : ℝ) + 1) * z * (1 + z) ^ k := by
  have hsub : |z - (k : ℝ)| ≤ z + (k : ℝ) := by
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  rcases k with _ | k
  · simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one, zero_add, one_mul]
    rw [abs_of_nonneg hz]
  · push_cast at hsub ⊢
    have hz1 : (0:ℝ) ≤ 1 + z := by linarith
    have hstep : z ^ k ≤ (1+z)^k := pow_le_pow_left₀ hz (by linarith) k
    have hb : z + ((k:ℝ)+1) ≤ ((k:ℝ)+2) * (1+z) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, hz]
    have hstep2 : z^k * (z + ((k:ℝ)+1)) ≤ (1+z)^k * (((k:ℝ)+2) * (1+z)) := by
      calc z^k * (z + ((k:ℝ)+1)) ≤ (1+z)^k * (z + ((k:ℝ)+1)) :=
            mul_le_mul_of_nonneg_right hstep (by linarith [Nat.cast_nonneg (α := ℝ) k])
        _ ≤ (1+z)^k * (((k:ℝ)+2) * (1+z)) := mul_le_mul_of_nonneg_left hb (pow_nonneg hz1 k)
    calc |z ^ (k + 1) * (z - ((k:ℝ)+1))|
        = z * (z ^ k * |z - ((k:ℝ)+1)|) := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hz _), pow_succ]; ring
      _ ≤ z * (z ^ k * (z + ((k:ℝ)+1))) := by
            refine mul_le_mul_of_nonneg_left ?_ hz
            exact mul_le_mul_of_nonneg_left hsub (pow_nonneg hz k)
      _ ≤ z * ((1+z)^k * (((k:ℝ)+2) * (1+z))) := mul_le_mul_of_nonneg_left hstep2 hz
      _ = ((k:ℝ) + 1 + 1) * z * (1 + z) ^ (k+1) := by rw [pow_succ]; ring

/-- The weighted bound `|z^k h^{(k)}(z)| ≤ k!(k+1)·z/(1+z)²` for the profile
`h = hKer` (`Work.Spaces.hKerClosed` is its closed-form `k`-th derivative), `z ≥ 0`. -/
private lemma zpow_hKerClosed_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * Work.Spaces.hKerClosed k z|
      ≤ (k.factorial : ℝ) * ((k : ℝ) + 1) * (z * ((1 + z)⁻¹) ^ 2) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hne : (1 + z) ≠ 0 := ne_of_gt h1z
  have hpow : (1 + z)^k * ((1 + z)⁻¹)^(k + 2) = ((1 + z)⁻¹)^2 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
  have hstep : z ^ k * |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z * (1 + z)^k := by
    have := zpow_mul_sub_le k hz
    rwa [abs_mul, abs_of_nonneg (pow_nonneg hz k)] at this
  have hsub : |z ^ k * Work.Spaces.hKerClosed k z|
      = (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) * ((1 + z)⁻¹)^(k + 2) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz k), abs_hKerClosed k hz]
    ring
  rw [hsub]
  have hnn : (0:ℝ) ≤ ((1 + z)⁻¹)^(k + 2) :=
    pow_nonneg (inv_nonneg.mpr (le_of_lt h1z)) _
  have hk : (0:ℝ) ≤ (k.factorial : ℝ) := by positivity
  calc (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) * ((1 + z)⁻¹)^(k + 2)
      ≤ (k.factorial : ℝ) * (((k : ℝ) + 1) * z * (1 + z)^k) * ((1 + z)⁻¹)^(k + 2) := by
        gcongr
    _ = (k.factorial : ℝ) * ((k : ℝ) + 1) * (z * ((1 + z)⁻¹)^2) := by
        rw [← hpow]; ring

/-- The closed form of the iterated derivatives of `Hz = 2·id·h'` (Leibniz, since
`(id)'' = 0`): `Hz^{(n)}(y) = 2·(y·h^{(n+1)}(y) + n·h^{(n)}(y))` for `y > -1`. -/
private lemma iter_deriv_Hz (n : ℕ) {z : ℝ} (hz : -1 < z) :
    deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z
      = 2 * (z * Work.Spaces.hKerClosed (n + 1) z
             + (n : ℝ) * Work.Spaces.hKerClosed n z) := by
  have hmain : ∀ m : ℕ, ∀ y : ℝ, -1 < y →
      deriv^[m] Work.FTS.Nonlinear.FstarPkg.Hz y
        = 2 * (y * Work.Spaces.hKerClosed (m + 1) y
               + (m : ℝ) * Work.Spaces.hKerClosed m y) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      simp only [Function.iterate_zero_apply]
      have h1 : deriv Work.Spaces.hKer y = Work.Spaces.hKerClosed 1 y := by
        show deriv (fun y : ℝ => y / (1 + y) ^ 2) y = Work.Spaces.hKerClosed 1 y
        exact Work.Spaces.iter_deriv_hKerClosed 1 y hy
      rw [Work.FTS.Nonlinear.FstarPkg.Hz_eq_mul_deriv hy, h1]
      simp
    | succ m ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      have hev : deriv^[m] Work.FTS.Nonlinear.FstarPkg.Hz =ᶠ[𝓝 y]
          (fun t : ℝ => 2 * (t * Work.Spaces.hKerClosed (m + 1) t
            + (m : ℝ) * Work.Spaces.hKerClosed m t)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
        exact ih t ht
      rw [hev.deriv_eq]
      have hyne : y ≠ -1 := by linarith
      have hd1 : HasDerivAt (fun t : ℝ => t * Work.Spaces.hKerClosed (m + 1) t)
          (1 * Work.Spaces.hKerClosed (m + 1) y + y * Work.Spaces.hKerClosed ((m + 1) + 1) y) y :=
        (hasDerivAt_id y).mul (Work.Spaces.hasDerivAt_hKerClosed (m + 1) hyne)
      have hd2 : HasDerivAt (fun t : ℝ => (m : ℝ) * Work.Spaces.hKerClosed m t)
          ((m : ℝ) * Work.Spaces.hKerClosed (m + 1) y) y :=
        (Work.Spaces.hasDerivAt_hKerClosed m hyne).const_mul (m : ℝ)
      have hd : HasDerivAt
          (fun t : ℝ => 2 * (t * Work.Spaces.hKerClosed (m + 1) t
            + (m : ℝ) * Work.Spaces.hKerClosed m t))
          (2 * (1 * Work.Spaces.hKerClosed (m + 1) y + y * Work.Spaces.hKerClosed ((m + 1) + 1) y
            + (m : ℝ) * Work.Spaces.hKerClosed (m + 1) y)) y :=
        (hd1.add hd2).const_mul 2
      rw [hd.deriv]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  exact hmain n z hz

/-- The weighted `z`-derivative bounds of the radial factor `Hz z = 2z(1-z)/(1+z)^3` of `D_z F_*`: for every order `n ≤ 4` and every `z ≥ 0`, `|z^n · Hz^{(n)}(z)| ≤ C · z/(1+z)^2`, with `C` universal. Reviewers computed the ratios `|z^n Hz^{(n)}(z)|(1+z)^2/z` in closed form as `2|z−1|/(z+1)`, `2|z²−4z+1|/(z+1)²`, `4z|z²−7z+4|/(1+z)³`, `12z²|z²−10z+9|/(1+z)⁴`, `48z³|z²−13z+16|/(1+z)⁵` for `n = 0..4`, all bounded on `[0,∞)`; `C = 100` is safe. Route hint: `Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound` derives inside its proof the closed form `deriv^[n] Hz y = 2*(y*hKerClosed (n+1) y + n*hKerClosed n y)` on `(-1,∞)` (with `Work.Spaces.hKerClosed k z = (-1)^k k! (z-k) (1+z)^{-(k+2)}`, `Work.Spaces.hasDerivAt_hKerClosed`, `Work.Spaces.iter_deriv_hKerClosed`), from which `z^n deriv^[n] Hz z = 2*z^n*(1+z)^{-(n+3)}*P n z` with the explicit quadratic `P n z = (-1)^(n+1)*(n+1)!*z*(z-n-1) + n*(-1)^n*n!*(z-n)*(1+z)`. (Namespace: `Work.FTS.Nonlinear.Pieces.RNP.row19`.) -/
theorem abs_zpow_deriv_Hz_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |z ^ n * deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z|
      ≤ C * (z / (1 + z) ^ 2) := by
  refine ⟨10000, by norm_num, fun n hn z hz => ?_⟩
  have hz1 : -1 < z := by linarith
  have hZnn : 0 ≤ z * ((1 + z)⁻¹)^2 := mul_nonneg hz (sq_nonneg _)
  rw [iter_deriv_Hz n hz1]
  have hsplit : z ^ n * (2 * (z * Work.Spaces.hKerClosed (n + 1) z
        + (n : ℝ) * Work.Spaces.hKerClosed n z))
      = 2 * (z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)) := by
    rw [pow_succ]; ring
  rw [hsplit, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hA : |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z|
      ≤ ((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1) * (z * ((1+z)⁻¹)^2) :=
    zpow_hKerClosed_le (n+1) hz
  have hB : |(n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)|
      ≤ (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1) * (z * ((1+z)⁻¹)^2)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left (zpow_hKerClosed_le n hz) (Nat.cast_nonneg n)
  -- the numerical constant, for `n ≤ 4`
  have hnum : 2 * (((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1)
      + (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1))) ≤ 10000 := by
    interval_cases n <;> norm_num
  have hconv : z * ((1+z)⁻¹)^2 = z / (1+z)^2 := by rw [div_eq_mul_inv, inv_pow]
  have hmain : 2 * |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)|
      ≤ 10000 * (z * ((1+z)⁻¹)^2) := by
    have h1 : |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)| ≤
        ((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1) * (z * ((1+z)⁻¹)^2)
          + (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1) * (z * ((1+z)⁻¹)^2)) :=
      le_trans (abs_add_le _ _) (add_le_add hA hB)
    nlinarith [h1, hnum, hZnn]
  rw [hconv] at hmain
  exact hmain

end Work.FTS.Nonlinear.Pieces.RNP.row19
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggEnvTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false

/-! ## Elementary angular facts -/

theorem integrableOn_one_Iθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
  MeasureTheory.integrableOn_const (μ := volume)
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem integral_one_Iθ : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
    Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

theorem sqrt_pi_half_le_two : Real.sqrt (Real.pi / 2) ≤ 2 := by
  calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## The angular Cauchy–Schwarz step -/

/-- **The angular Cauchy–Schwarz step in `∫⁻`-form.**  For a slice `u` which is a.e. strongly
measurable and whose square is integrable,
`∫⁻_θ ofReal |u θ| ≤ ofReal (2 √(∫_θ u θ²))`; the constant `2` comes from
`∫_{Iθ} 1 = π/2 ≤ 4` and `√(π/2) ≤ 2`. -/
theorem inner_abs_lintegral_le {u : ℝ → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hint : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |u θ|)
      ≤ ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  have hui : IntegrableOn (fun θ => |u θ|) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => (1 + (u θ) ^ 2) / 2) ?_ hu.norm ?_
    · exact (integrableOn_one_Iθ.add hint).mul_const (2 : ℝ)⁻¹
    · exact Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_abs]
        have h := sq_nonneg (|u θ| - 1)
        nlinarith [sq_abs (u θ), h]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hui
    (Eventually.of_forall fun θ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : IntegrableOn (fun θ => (|u θ|) ^ 2) Work.Spaces.Iθ := by
    simpa only [sq_abs] using hint
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun θ => |u θ|) (g := fun _ => (1 : ℝ)) hu.norm aestronglyMeasurable_const h2
    (by simpa using integrableOn_one_Iθ)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |u θ| :=
    MeasureTheory.integral_nonneg fun θ => abs_nonneg _
  have hsq : (∫ θ in Work.Spaces.Iθ, (|u θ|) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => sq_abs (u θ))
  have hg2 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
    rw [show (1 : ℝ) ^ 2 = 1 by norm_num, integral_one_Iθ]
  calc (∫ θ in Work.Spaces.Iθ, |u θ|)
      = |∫ θ in Work.Spaces.Iθ, |u θ| * 1| := by
        simp only [mul_one]
        exact (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (|u θ|) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
        rw [hsq, hg2]
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left sqrt_pi_half_le_two (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by ring

/-- `√(w z) = (1+z)/z` for `z > 0`, `w z = (1+z)²/z²`. -/
theorem sqrt_w_eq {z : ℝ} (hz : 0 < z) : Real.sqrt (Work.Spaces.w z) = (1 + z) / z := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h2, Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq h1.le, Real.sqrt_sq hz.le]

/-- The two algebraic identities behind the radial Cauchy–Schwarz steps, for `z > 0`:
`z⁻¹ · (a / w z) = a · (z/(1+z)²)` and `√(a/w z) = √a · (z/(1+z))` for `a ≥ 0`. -/
theorem zinv_div_w (z a : ℝ) (hz : 0 < z) :
    z⁻¹ * (a / Work.Spaces.w z) = a * (z / (1 + z) ^ 2) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 + z) ≠ 0 := by positivity
  rw [Work.Spaces.w]
  field_simp

theorem sqrt_div_w (z a : ℝ) (hz : 0 < z) (ha : 0 ≤ a) :
    Real.sqrt (a / Work.Spaces.w z) = Real.sqrt a * (z / (1 + z)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 + z) ≠ 0 := by positivity
  rw [Real.sqrt_div ha, sqrt_w_eq hz]
  field_simp

/-! ## The radial Cauchy–Schwarz steps -/

/-- **The radial Cauchy–Schwarz step, one angular factor.**

If `w z · S z ≤ Φ z` for `z > 0` and `Φ ≥ 0` is integrable on `(0,∞)`, then
`∫⁻_z z⁻¹ · ofReal (c √(S z)) ≤ ofReal (c √(∫_z Φ z))`. -/
theorem zinv_lintegral_sqrt_le {Φ S : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z)
    (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot : ∀ z, 0 < z → Work.Spaces.w z * S z ≤ Φ z) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * Real.sqrt (S z)))
      ≤ ENNReal.ofReal (c * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hΦsm : AEStronglyMeasurable Φ (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hΦint.aestronglyMeasurable
  have hdiv : AEStronglyMeasurable (fun z => 1 / (1 + z)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun z hz => by
        have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
        simp only [Pi.add_apply, id_eq]
        positivity)).aestronglyMeasurable
      measurableSet_Ioi
  have hFsm : AEStronglyMeasurable (fun z => Real.sqrt (Φ z) / (1 + z))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := (Real.continuous_sqrt.comp_aestronglyMeasurable hΦsm).mul hdiv
    refine h.congr ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z _ => by simp only [Pi.mul_apply, div_eq_mul_inv, one_mul])
  have hF : IntegrableOn (fun z => Real.sqrt (Φ z) / (1 + z)) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (g := fun z => (Φ z + 1 / (1 + z) ^ 2) / 2) ?_ hFsm ?_
    · exact (hΦint.add Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_one_div_one_add_sq).mul_const
        (2 : ℝ)⁻¹
    · refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
      have hz0 : 0 < z := hz
      have h1 : (0 : ℝ) < 1 + z := by linarith
      have hsq : ((1 + z)⁻¹) ^ 2 = 1 / (1 + z) ^ 2 := by rw [inv_pow, one_div]
      have hkey := two_mul_le_add_sq (Real.sqrt (Φ z)) ((1 + z)⁻¹)
      rw [Real.sq_sqrt (hΦnn z hz0), hsq] at hkey
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) h1.le)]
      have hdiv : Real.sqrt (Φ z) / (1 + z) = Real.sqrt (Φ z) * (1 + z)⁻¹ := rfl
      rw [hdiv]
      linarith
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * Real.sqrt (S z))
        ≤ ENNReal.ofReal (c * (Real.sqrt (Φ z) / (1 + z))) := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz0 : 0 < z := hz
    have hw : 0 < Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz0
    have hinv : 0 ≤ z⁻¹ := inv_nonneg.mpr hz0.le
    have hle : z⁻¹ * Real.sqrt (S z) ≤ Real.sqrt (Φ z) / (1 + z) := by
      have hSw : Real.sqrt (S z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
        rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
        refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
        rw [mul_comm]
        exact hslot z hz0
      calc z⁻¹ * Real.sqrt (S z) ≤ z⁻¹ * (Real.sqrt (Φ z) * (z / (1 + z))) :=
            mul_le_mul_of_nonneg_left hSw hinv
        _ = Real.sqrt (Φ z) / (1 + z) := by field_simp
    rw [← ENNReal.ofReal_mul hinv]
    refine ENNReal.ofReal_le_ofReal ?_
    calc z⁻¹ * (c * Real.sqrt (S z)) = c * (z⁻¹ * Real.sqrt (S z)) := by ring
      _ ≤ c * (Real.sqrt (Φ z) / (1 + z)) := mul_le_mul_of_nonneg_left hle hc
  refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
  have hG : IntegrableOn (fun z => c * (Real.sqrt (Φ z) / (1 + z))) (Set.Ioi (0 : ℝ)) :=
    hF.const_mul c
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => mul_nonneg hc (div_nonneg (Real.sqrt_nonneg _) (by linarith [Set.mem_Ioi.mp hz]))))]
  rw [MeasureTheory.integral_const_mul]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc)
  have hsqint : IntegrableOn (fun z => (Real.sqrt (Φ z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hΦint.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => (Real.sq_sqrt (hΦnn z (Set.mem_Ioi.mp hz))).symm))
  have hG2int : IntegrableOn (fun z => (1 / (1 + z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_one_div_one_add_sq.congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z _ => by simp only [div_pow, one_pow]))
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun z => Real.sqrt (Φ z)) (g := fun z => 1 / (1 + z))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hΦsm) hdiv hsqint hG2int
  have hcongr : (∫ z in Set.Ioi (0 : ℝ), (Real.sqrt (Φ z)) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), Φ z :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z hz => Real.sq_sqrt (hΦnn z (Set.mem_Ioi.mp hz)))
  have hG2eq : (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => by simp only [div_pow, one_pow])
  have hnn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z)) :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
        mul_nonneg (Real.sqrt_nonneg _)
          (div_nonneg zero_le_one (by linarith [Set.mem_Ioi.mp hz]))))
  calc ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) / (1 + z)
      = ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (fun z _ => by rw [div_eq_mul_inv, one_div])
    _ = |∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z))| :=
        (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (Real.sqrt (Φ z)) ^ 2)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) := hcs
    _ = Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) := by rw [hcongr]
    _ ≤ Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one, hG2eq]
        exact (Work.FTS.Nonlinear.Pieces.rl1Tools.integral_one_div_one_add_sq).le
    _ = Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z) := mul_one _

/-- **The radial Cauchy–Schwarz step, two angular factors** (the `FK(g)`-rows).

If `w z · Sᵢ z ≤ Φ z` for `i = 1,2` and `Φ ≥ 0` is integrable, then
`∫⁻_z z⁻¹ ofReal (c √(S₁ z) √(S₂ z)) ≤ ofReal (c · (1/4) ∫_z Φ z)`: the product of the two
angular factors is at most `Φ z/w z`, so the integrand is at most
`c Φ z · z/(1+z)² ≤ c Φ z/4`. -/
theorem zinv_lintegral_prod_sqrt_le {Φ S₁ S₂ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z)
    (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot1 : ∀ z, 0 < z → Work.Spaces.w z * S₁ z ≤ Φ z)
    (hslot2 : ∀ z, 0 < z → Work.Spaces.w z * S₂ z ≤ Φ z) :
    (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))))
      ≤ ENNReal.ofReal (c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))
        ≤ ENNReal.ofReal (c * (Φ z * (z / (1 + z) ^ 2))) := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz0 : 0 < z := hz
    have hw : 0 < Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz0
    have hinv : 0 ≤ z⁻¹ := inv_nonneg.mpr hz0.le
    have h1 : Real.sqrt (S₁ z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
      rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
      refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
      rw [mul_comm]
      exact hslot1 z hz0
    have h2 : Real.sqrt (S₂ z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
      rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
      refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
      rw [mul_comm]
      exact hslot2 z hz0
    have hΦ0 : 0 ≤ Real.sqrt (Φ z) * (z / (1 + z)) :=
      mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hz0.le (by linarith))
    have hprod : Real.sqrt (S₁ z) * Real.sqrt (S₂ z) ≤ Φ z / Work.Spaces.w z := by
      calc Real.sqrt (S₁ z) * Real.sqrt (S₂ z)
          ≤ (Real.sqrt (Φ z) * (z / (1 + z))) * (Real.sqrt (Φ z) * (z / (1 + z))) :=
            mul_le_mul h1 h2 (Real.sqrt_nonneg _) hΦ0
        _ = (Real.sqrt (Φ z) * (z / (1 + z))) ^ 2 := (sq _).symm
        _ = (Real.sqrt (Φ z)) ^ 2 * (z / (1 + z)) ^ 2 := by rw [mul_pow]
        _ = Φ z / Work.Spaces.w z := by
            rw [Real.sq_sqrt (hΦnn z hz0)]
            rw [Work.Spaces.w]
            field_simp
    have hle : z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))
        ≤ Φ z * (z / (1 + z) ^ 2) := by
      calc z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))
          ≤ z⁻¹ * (Φ z / Work.Spaces.w z) := mul_le_mul_of_nonneg_left hprod hinv
        _ = Φ z * (z / (1 + z) ^ 2) := zinv_div_w z (Φ z) hz0
    rw [← ENNReal.ofReal_mul hinv]
    refine ENNReal.ofReal_le_ofReal ?_
    calc z⁻¹ * (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))
        = c * (z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))) := by ring
      _ ≤ c * (Φ z * (z / (1 + z) ^ 2)) := mul_le_mul_of_nonneg_left hle hc
  refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
  have hcontq : ContinuousOn (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz])))
  have hG : IntegrableOn (fun z => c * (Φ z * (z / (1 + z) ^ 2))) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (g := fun z => c * (Φ z * (1 / 4))) ?_ ?_ ?_
    · exact (hΦint.mul_const (1 / 4)).const_mul c
    · exact ((hΦint.aestronglyMeasurable.mul
        (hcontq.aestronglyMeasurable measurableSet_Ioi)).const_mul c)
    · refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
      have hz0 : 0 < z := hz
      have h1z : (0 : ℝ) < 1 + z := by linarith
      have hq : z / (1 + z) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg (1 - z)]
      have hnonneg : (0 : ℝ) ≤ c * (Φ z * (z / (1 + z) ^ 2)) :=
        mul_nonneg hc (mul_nonneg (hΦnn z hz0)
          (div_nonneg hz0.le (by positivity)))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (hΦnn z hz0)) hc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => mul_nonneg hc (mul_nonneg (hΦnn z (Set.mem_Ioi.mp hz))
        (div_nonneg (Set.mem_Ioi.mp hz).le (by positivity)))))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [MeasureTheory.integral_const_mul]
  have hmono : (∫ z in Set.Ioi (0 : ℝ), Φ z * (z / (1 + z) ^ 2))
      ≤ ∫ z in Set.Ioi (0 : ℝ), Φ z * (1 / 4) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z hz => mul_nonneg (hΦnn z (Set.mem_Ioi.mp hz))
          (div_nonneg (Set.mem_Ioi.mp hz).le (by positivity))))
      (hΦint.mul_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    have h1z : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    have hq : z / (1 + z) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg (1 - z)]
    exact mul_le_mul_of_nonneg_left hq (hΦnn z (Set.mem_Ioi.mp hz))
  calc c * (∫ z in Set.Ioi (0 : ℝ), Φ z * (z / (1 + z) ^ 2))
      ≤ c * (∫ z in Set.Ioi (0 : ℝ), Φ z * (1 / 4)) := mul_le_mul_of_nonneg_left hmono hc
    _ = c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z) := by
        rw [MeasureTheory.integral_mul_const]
        ring

/-! ## The `ℋ⁴`-integrand slice `Φ` of `g` -/

theorem Phi_int {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) :
    IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      (Set.Ioi (0 : ℝ)) :=
  hmem.2.mono_set Set.Ioi_subset_Ici_self

theorem Phi_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
  MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ

theorem Phi_integral {α : ℝ} {g : ℝ → ℝ → ℝ} :
    (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = Work.Spaces.HkSq α 4 g :=
  (Work.FTS.Nonlinear.Pieces.rl1Tools.HkSq_eq_integral_Ioi α g).symm

theorem sqrt_Phi_integral {α : ℝ} {g : ℝ → ℝ → ℝ} :
    Real.sqrt (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g r θ) = Work.FTS.Nonlin.Xn α g := by
  rw [Phi_integral]
  rfl

/-! ## The angular slice masses of `g`, `D_θg`, `D_zg` -/

theorem slice_sq_int_g {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · exact (((hsm.curry_θ (by simp only [Set.mem_Ioi]; linarith)).continuousOn).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw1 : 1 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hz
    have hw0 : 0 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg z
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hpt : (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.w2_sq_le_HkIntegrand α hz hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpt, hw2, sq_nonneg (g z θ)]

theorem aesm_g_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => g z θ) (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => g z θ) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact ((hsm.curry_θ (by simp only [Set.mem_Ioi]; linarith)).continuousOn)
    |>.aestronglyMeasurable measurableSet_Ioo

theorem slot_g_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  have h2 := Work.FTS.Nonlinear.Pieces.rl1Tools.wsq_mul_slice_le α hα hsm hmem r hr
  have hw1 : 1 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hr
  have hw0 : 0 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r
  have hS0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hw12 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
  calc Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
      ≤ (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hw12 hS0
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := h2

/-- The `D_θ`-mass with the `sin(2θ)^{-γ}` weight is integrable: it is dominated by the
`ℋ⁴`-integrand (`w² · (D_θg)² sin(2θ)^{-γ} ≤ HkIntegrand`). -/
theorem slice_Dth_gam_int {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dth g z θ) ^ 2
      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dth g z θ) ^ 2
    * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩) |>.div_const _) ?_ ?_
  · refine (((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt
          (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ))))).aestronglyMeasurable
      measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw : 0 < (Work.Spaces.w z) ^ 2 := by
      have := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz
      positivity
    have hpt : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dth g z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.w2_Dth_sq_le_HkIntegrand α hα hz hθ
    have hnn : 0 ≤ (Work.Spaces.Dth g z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, le_div_iff₀ hw]
    calc (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
          ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hpt

theorem slice_sq_int_Dth {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dth g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dth g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · exact ((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hd : (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.Dth_sq_le_HkIntegrand α hα hz hθ
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    have hrp : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _)
        (show -(Work.Spaces.gam α) ≤ 0 by linarith [Work.Spaces.gam_pos hα])
      rwa [Real.rpow_zero] at h
    have hle : (Work.Spaces.Dth g z θ) ^ 2
        ≤ (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      nlinarith [sq_nonneg (Work.Spaces.Dth g z θ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    linarith

theorem aesm_Dth_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => Work.Spaces.Dth g z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => Work.Spaces.Dth g z θ)
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact (Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz)
    |>.aestronglyMeasurable measurableSet_Ioo

/-- `w r · (∫_θ (D_θg)²) ≤ ∫_θ HkIntegrand`. -/
theorem slot_Dth_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  have h2 := Work.FTS.Nonlinear.Pieces.rl1Tools.wsq_mul_slice_Dth_le α hα hsm hmem r hr
  have hTint := slice_Dth_gam_int hα hsm hmem r hr
  have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) hTint ?_
    change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Dth g r θ) ^ 2
        ≤ (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    have hrp : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _)
        (show -(Work.Spaces.gam α) ≤ 0 by linarith [Work.Spaces.gam_pos hα])
      rwa [Real.rpow_zero] at h
    nlinarith [sq_nonneg (Work.Spaces.Dth g r θ)]
  have hw1 : 1 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hr
  have hw0 : 0 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r
  have hw12 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
  have hS0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  calc Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hw12 hS0
    _ ≤ (Work.Spaces.w r) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := h2

theorem slice_sq_int_Dz {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dz g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dz g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.Dz g z θ)
        (Set.Ioo 0 (π / 2)) :=
      Work.FTS.LocData.contDiffOn_slice_θ (hsm.DzIter 1) (by simp only [Set.mem_Ioi]; linarith)
    exact (hcd.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw1 : 1 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hz
    have hpt : Work.Spaces.w z * (Work.Spaces.Dz g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.slot_Dz α hz hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpt, hw1, sq_nonneg (Work.Spaces.Dz g z θ)]

theorem aesm_Dz_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => Work.Spaces.Dz g z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => Work.Spaces.Dz g z θ)
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.Dz g z θ)
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ (hsm.DzIter 1) (by simp only [Set.mem_Ioi]; linarith)
  exact hcd.continuousOn.aestronglyMeasurable measurableSet_Ioo

theorem slot_Dz_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => mul_nonneg (Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r) (sq_nonneg _)))
    (hmem.1 r hr.le) ?_
  change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    Work.Spaces.w r * (Work.Spaces.Dz g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Tools.slot_Dz α hr hθ)

/-! ## The pointwise size of the angular moment `FK g` -/

theorem K_continuous : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  unfold Work.Spaces.K
  fun_prop

theorem K_abs_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hc : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

theorem fk_pointwise_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → |Work.Construction.FK g z|
      ≤ 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
  intro z hz
  have hgint := slice_sq_int_g hsm hmem z hz
  have hgsm := aesm_g_slice hsm z hz
  have hKsm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) :=
    K_continuous.aestronglyMeasurable
  have hgabs : IntegrableOn (fun θ => |g z θ|) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => (1 + (g z θ) ^ 2) / 2) ?_ hgsm.norm ?_
    · exact (integrableOn_one_Iθ.add hgint).mul_const (2 : ℝ)⁻¹
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_abs]
      have h := sq_nonneg (|g z θ| - 1)
      nlinarith [sq_abs (g z θ), h]
  have hgabs2 : Integrable (fun θ => (|g z θ|) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    Integrable.congr (show Integrable (fun θ => (g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
      from hgint) (Eventually.of_forall fun θ => (sq_abs (g z θ)).symm)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun θ => |g z θ|) (g := fun _ => (1 : ℝ)) hgsm.norm aestronglyMeasurable_const
    hgabs2 (by
      have h : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
        integrableOn_one_Iθ
      exact h.congr (Eventually.of_forall fun x => by norm_num))
  have hCS : (∫ θ in Work.Spaces.Iθ, |g z θ|)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |g z θ| :=
      MeasureTheory.integral_nonneg fun θ => abs_nonneg _
    have habs : |∫ θ in Work.Spaces.Iθ, |g z θ| * 1| = ∫ θ in Work.Spaces.Iθ, |g z θ| := by
      simp only [mul_one]
      exact abs_of_nonneg hnn
    have hg2 : (∫ θ in Work.Spaces.Iθ, (|g z θ|) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => sq_abs (g z θ))
    have h1 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
      rw [show (1 : ℝ) ^ 2 = 1 by norm_num, integral_one_Iθ]
    rw [habs, hg2, h1] at hcs
    exact hcs
  have hInt : IntegrableOn (fun θ => g z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => 3 * |g z θ|) (hgabs.const_mul 3)
      (hgsm.mul hKsm) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_mul]
    calc |g z θ| * |Work.Spaces.K θ| ≤ |g z θ| * 3 :=
          mul_le_mul_of_nonneg_left (K_abs_le_three θ) (abs_nonneg _)
      _ = 3 * |g z θ| := by ring
  have h1 : |Work.Construction.FK g z| ≤ ∫ θ in Work.Spaces.Iθ, 3 * |g z θ| := by
    rw [Work.Construction.FK]
    refine le_trans (abs_integral_le_integral_abs (f := fun θ => g z θ * Work.Spaces.K θ)) ?_
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
      (hgabs.const_mul 3) ?_
    filter_upwards with θ
    calc |g z θ * Work.Spaces.K θ| = |g z θ| * |Work.Spaces.K θ| := abs_mul _ _
      _ ≤ |g z θ| * 3 := mul_le_mul_of_nonneg_left (K_abs_le_three θ) (abs_nonneg _)
      _ = 3 * |g z θ| := by ring
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * |g z θ|)
      ≤ 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2)) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hCS (by norm_num)
  calc |Work.Construction.FK g z| ≤ ∫ θ in Work.Spaces.Iθ, 3 * |g z θ| := h1
    _ ≤ 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2)) := h2
    _ = 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by ring

/-! ## The two row engines -/

theorem ggRow_single {N B : ℝ → ℝ → ℝ} {Φ S : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z) (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot : ∀ z, 0 < z → Work.Spaces.w z * S z ≤ Φ z)
    (hBS : ∀ z, 0 < z → (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) ≤ S z)
    (hBsm : ∀ z, 0 < z → AEStronglyMeasurable (fun θ => B z θ)
      (volume.restrict Work.Spaces.Iθ))
    (hBint : ∀ z, 0 < z → IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ)
    (hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * N z θ| ≤ c * |B z θ|) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N z θ|))
      ≤ ENNReal.ofReal (2 * c * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hinner : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N z θ|)
        ≤ ENNReal.ofReal (2 * c * Real.sqrt (S z)) := by
    intro z hz
    have hz0 : 0 < z := hz
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * |B z θ|) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hpt z hz] with θ hθ
          exact ENNReal.ofReal_le_ofReal hθ
      _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal |B z θ| :=
          MeasureTheory.lintegral_congr_ae
            (Eventually.of_forall fun θ => ENNReal.ofReal_mul hc)
      _ = ENNReal.ofReal c * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c
            * ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) :=
          mul_le_mul_right (inner_abs_lintegral_le (hBsm z hz0) (hBint z hz0)) _
      _ = ENNReal.ofReal (c * (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2))) :=
          (ENNReal.ofReal_mul hc).symm
      _ ≤ ENNReal.ofReal (2 * c * Real.sqrt (S z)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq : Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) ≤ Real.sqrt (S z) :=
            Real.sqrt_le_sqrt (hBS z hz0)
          nlinarith [Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2), hsq, hc]
  refine (MeasureTheory.lintegral_mono_ae ?_).trans
    (zinv_lintegral_sqrt_le (c := 2 * c) (by linarith) hΦnn hΦint hslot)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  exact mul_le_mul_right (hinner z hz) (ENNReal.ofReal z⁻¹)

theorem ggRow_prod {N : ℝ → ℝ → ℝ} {Φ S₁ S₂ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z) (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot1 : ∀ z, 0 < z → Work.Spaces.w z * S₁ z ≤ Φ z)
    (hslot2 : ∀ z, 0 < z → Work.Spaces.w z * S₂ z ≤ Φ z)
    (hinner : ∀ z ∈ Set.Ioi (0 : ℝ), (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |N z θ|)
        ≤ ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |N z θ|))
      ≤ ENNReal.ofReal (c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  refine (MeasureTheory.lintegral_mono_ae ?_).trans
    (zinv_lintegral_prod_sqrt_le hc hΦnn hΦint hslot1 hslot2)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  exact mul_le_mul_right (hinner z hz) (ENNReal.ofReal z⁻¹)

end Work.FTS.Nonlinear.Pieces.rl1Pieces
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.AprioriOpen.RegQApiOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Nonlin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Scalar homogeneity of the iterated operators (unconditional)

`deriv (c · u) = c · deriv u` holds with no differentiability hypothesis (both sides vanish when
`u` is not differentiable at the point and `c ≠ 0`; the claim is trivial for `c = 0`). -/

private theorem deriv_const_mul' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul']

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul']

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- **The mixed operators are scalar homogeneous** (unconditionally). -/
theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Additivity of the iterated operators on the open quadrant (`SmoothQuad` data) -/

private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter j a z θ + Work.Spaces.DzIter j b z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **The mixed operators `D_z^jD_θ^i` are additive on the open quadrant** for `SmoothQuad` data. -/
theorem mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**  The closed-quadrant version
`Work.FTS.LocData.HkMem_of_majorant` requires the domination at every point of
`[0,∞) × [0,π/2]`; here it is only required for almost every interior angle, which is what
the additivity of the `D`-operators on the open quadrant delivers. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

/-! ## `RegQ` is monotone in the order -/

private theorem HkIntegrand_mono_le_aux (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    ∀ d : ℕ,
      Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α (l + d) f z θ := by
  intro d
  induction d with
  | zero => simp
  | succ n ih =>
      have h2 : Work.Spaces.HkIntegrand α (l + n) f z θ
          ≤ Work.Spaces.HkIntegrand α (l + n + 1) f z θ :=
        Work.Spaces.HkIntegrand_mono α (l + n) f z θ
      have heq : l + n + 1 = l + (n + 1) := by omega
      rw [heq] at h2
      exact le_trans ih h2

private theorem HkIntegrand_mono_le (α : ℝ) {l k : ℕ} (hkl : l ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have h := HkIntegrand_mono_le_aux α l f z θ (k - l)
  rwa [Nat.add_sub_of_le hkl] at h

private theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`RegQ` descends in the order**: `RegQ α k f → l ≤ k → RegQ α l f`. -/
theorem regQ_mono {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (hf : RegQ α k f) : RegQ α l f := by
  obtain ⟨hsm, hmem, htr⟩ := hf
  refine ⟨hsm, ?_, fun a b hab => htr a b (le_trans hab hkl)⟩
  refine HkMem_of_majorant_ae α l
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand (smoothOpen_of_smoothQuad hsm) α l)
    hmem.1 hmem.2 ?_
  intro z _
  exact Eventually.of_forall fun θ => HkIntegrand_mono_le α hkl f z θ

/-! ## `RegQ` is closed under multiplication by a constant -/

private theorem bdryTraces_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (htr : BdryTraces α k f) : BdryTraces α k (fun z θ => c * f z θ) := by
  intro a b hab
  have hfab := htr a b hab
  have hfun : ∀ z θ, Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed b a f z θ := by
    intro z θ
    rw [mixed_const_mul]
  have hz : ∀ θ, (fun z => z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
        * Work.Spaces.w z) ^ 2)
      = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) := by
    intro θ
    funext z
    show z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ * Work.Spaces.w z) ^ 2
      = c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
    rw [hfun z θ]; ring
  have ht : ∀ z, (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2)
      = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    intro z
    funext θ
    show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2
      = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2)
    rw [hfun z θ]; ring
  constructor
  · intro θ hθ
    have h := hfab.1 θ hθ
    constructor
    · rw [hz θ]
      simpa using h.1.const_mul (c ^ 2)
    · rw [hz θ]
      simpa using h.2.const_mul (c ^ 2)
  · intro z hzmem
    have h := hfab.2 z hzmem
    constructor
    · rw [ht z]
      simpa using h.1.const_mul (c ^ 2)
    · rw [ht z]
      simpa using h.2.const_mul (c ^ 2)

/-- **`RegQ` is closed under multiplication by a constant.** -/
theorem regQ_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) : RegQ α k (fun z θ => c * f z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α k c hf.2.1, bdryTraces_smul c hf.2.2⟩

/-! ## `RegQ` is closed under addition -/

/-- Additivity of `BdryTraces`: by `mixed_add_quad` the boundary limits of the sum are those of
the sum of the limits, and `z ≥ 0` resp. `sin(2θ)^{1-γ} ≥ 0` let the squeeze theorem conclude. -/
theorem bdryTraces_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (htf : BdryTraces α k f) (htg : BdryTraces α k g) :
    BdryTraces α k (fun z θ => f z θ + g z θ) := by
  intro a b hab
  have hfab := htf a b hab
  have hgab := htg a b hab
  have hpt : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ :=
    fun z θ hz h1 h2 => mixed_add_quad hsmf hsmg b a z θ (by linarith) h1 h2
  -- the algebraic comparison of the weighted squares (open quadrant, hence nonnegative weights)
  have hwsq : ∀ z θ, (Work.Spaces.w z
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ)) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2 := by
    intro z θ
    nlinarith [sq_nonneg (Work.Spaces.w z * Work.Spaces.mixed b a f z θ
        - Work.Spaces.w z * Work.Spaces.mixed b a g z θ)]
  have hssq : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) ^ 2
      ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2)
        + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z θ hθ
    have h1 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ), h1]
  constructor
  · intro θ hθ
    have hA := hfab.1 θ hθ
    have hB := hgab.1 θ hθ
    have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimT : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) atTop (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hsq : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt (Set.mem_Ioi.mp hzmem)) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt (Set.mem_Ioi.mp hzmem)]
    have hsqT : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimT ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt hzmem) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt hzmem]
    exact ⟨hsq, hsqT⟩
  · intro z hzmem
    have hA := hfab.2 z hzmem
    have hB := hgab.2 z hzmem
    have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimL : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hmemGT : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hmemLT : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hsq : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [hmemGT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemGT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    have hsqL : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimL ?_ ?_
      · filter_upwards [hmemLT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemLT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    exact ⟨hsq, hsqL⟩

/-- **`ℋ^k` is closed under addition** for data which are `C^∞` on the open quadrant (the
open-quadrant copy of `Work.FTS.EllipticEst.HkMem_add_open`, proved with the additivity lemmas of
this file). -/
theorem HkMem_add_quad {α : ℝ} (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  refine HkMem_of_majorant_ae (α := α) (k := k) (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (Work.FTS.EllipticEst.smoothOpen_add (smoothOpen_of_smoothQuad hf)
        (smoothOpen_of_smoothQuad hg)) α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have h1 : MeasureTheory.IntegrableOn
        (fun z => 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        Work.Spaces.Iz := hmf.2.const_mul 2
    have h2 : MeasureTheory.IntegrableOn
        (fun z => 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        Work.Spaces.Iz := hmg.2.const_mul 2
    refine (h1.add h2).congr_fun ?_ measurableSet_Ici
    intro z hz
    change 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      = ∫ θ in Work.Spaces.Iθ, 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => f z θ + g z θ) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k g θ]
        norm_num
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      have hzm : -1 < z := by linarith
      have hθ1 : 0 < θ := hθ.1
      have hθ2 : θ < π / 2 := hθ.2
      have hRad : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ)
            z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [DzIter_add_quad hf hg i z θ hzm hθ1 hθ2]
        nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      have hMix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ)
              z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hij
        · rw [mixed_add_quad hf hg j i z θ hzm hθ1 hθ2]
          nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
        · norm_num
      rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
      rw [mul_add, mul_add]
      linarith [hRad, hMix]

/-- **`RegQ` is closed under addition.** -/
theorem regQ_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_add hf.1 hg.1,
    HkMem_add_quad k hf.1 hg.1 hf.2.1 hg.2.1,
    bdryTraces_add hf.1 hg.1 hf.2.2 hg.2.2⟩

/-! ## Derived closure properties -/

/-- `RegQ` contains the zero profile. -/
theorem regQ_zero (α : ℝ) (k : ℕ) : RegQ α k (fun _ _ : ℝ => (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  refine ⟨hsm, Work.FTS.EllipticEst.HkMem_zero α k, ?_⟩
  intro a b _
  have hmix : Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
    have h := mixed_const_mul (0 : ℝ) (fun _ _ : ℝ => (1 : ℝ)) b a
    simpa using h
  have hmix_pt : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
    fun z θ => congrFun (congrFun hmix z) θ
  constructor
  · intro θ _
    have hz : (fun z => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
        * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
      funext z
      show z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.w z) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [hz]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · intro z _
    have ht : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [ht]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-- `RegQ` is closed under negation. -/
theorem regQ_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hf : RegQ α k f) :
    RegQ α k (fun z θ => -f z θ) := by
  have h := regQ_smul (α := α) (k := k) (-1) hf
  simpa using h

/-- `RegQ` is closed under subtraction. -/
theorem regQ_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ - g z θ) := by
  have h := regQ_add hf (regQ_neg hg)
  simpa [sub_eq_add_neg] using h

/-- `RegQ` is closed under finite linear combinations. -/
theorem regQ_finset_sum {α : ℝ} {k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ → ℝ) (hF : ∀ i ∈ s, RegQ α k (F i)) :
    RegQ α k (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      exact regQ_zero α k
  | insert a s' ha ih =>
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]; rfl
      rw [hsum]
      refine regQ_add (regQ_smul (c a) (hF a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end Work.FTS.OpenPkg.AprioriOpen
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Aprof_wiln =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Negation and the `deriv`-iterates -/


/-! ## The value of `Aprof` at `0` -/


/-! ## The identification `Aprof α = −Gbar α (F_*)` on `z > 0` -/

/-- On `z ≥ 0` the singular term `G_*` is `−Θ/sin 2θ = −1/(2(1+z))`, so `Aprof α` —
which is `−(G_* + Ḡ) − Θ/sin 2θ` — equals `−Ḡ = −Dk (5/α) 0`. -/
theorem Aprof_eqOn_negDk {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    EqOn (Aprof α) (fun z => -Work.FTS.H2.PhiStarE.Dk (5 / α) 0 z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  have hL : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    L12_profile_eq hα hα1 hz0
  have hL' : Work.Elliptic.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := hL
  have hGS : Work.Elliptic.Gstar α (Work.Construction.Fstar α) z = -ThetaProfile z := by
    rw [Work.Elliptic.Gstar, hL', ThetaProfile]
    have h1z : (1 + z) ≠ 0 := by linarith
    field_simp
    ring
  have hGB : Work.Elliptic.Gbar α (Work.Construction.Fstar α) z
      = Work.FTS.H2.PhiStarE.Dk (5 / α) 0 z := by
    have h := Work.FTS.H2.PhiStarE.Gbar_eq_of_nonneg α hα hα1 hz0
    rw [h]
    simp only [Work.FTS.H2.PhiStarE.Dk_zero, Work.FTS.H2.PhiStarE.Pi_def]
  simp only [Aprof, GzProfile, Work.Elliptic.Gsing]
  rw [hGS, hGB]
  ring

/-! ## The weighted pointwise bound -/


/-! ## The `𝒲^{4,∞}` estimate -/


end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.GzProfile_ode =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem GzProfile_ode {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    GzOde α (GzProfile α) := by
  have hα1' : α ≤ 1 := by linarith
  -- The derivative of `z ↦ L₁₂(F_*)(z)`, from the explicit form `2α/(1+z)`.
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 (Work.Construction.Fstar α) z')
        (-(3 * Work.Elliptic.Fstar (Work.Construction.Fstar α) z / z)) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hev : (fun z' => Work.Elliptic.L12 (Work.Construction.Fstar α) z')
        =ᶠ[𝓝 z] (fun z' => 2 * α / (1 + z')) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
      have h := Work.Elliptic.L12_profile α hα hα1' z' (le_of_lt hz')
      rwa [show (fun w θ => α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.FM.Fstar w)
        = Work.Construction.Fstar α from rfl] at h
    have hder : HasDerivAt (fun z' : ℝ => 2 * α / (1 + z')) (-(2 * α) / (1 + z) ^ 2) z := by
      have hnum : HasDerivAt (fun _ : ℝ => 2 * α) 0 z := hasDerivAt_const z _
      have hden : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
        simpa using (hasDerivAt_id z).const_add 1
      have h := hnum.div hden (by linarith : (1 + z) ≠ 0)
      convert h using 1
      ring
    refine (hder.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    simp only [Work.FM.Fstar]
    field_simp
  -- `F_*` is differentiable on `z > 0`.
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar (Work.Construction.Fstar α))
        (deriv (Work.Elliptic.Fstar (Work.Construction.Fstar α)) z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    rw [hasDerivAt_deriv_iff]
    have hz1 : (1 : ℝ) + z ≠ 0 := by linarith
    have hden : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
      have h := (hasDerivAt_id z).const_add 1
      convert h.pow 2 using 1
      · funext u; simp
      · simp
    have hnum : HasDerivAt (fun z : ℝ => α * (2 * z)) (α * 2) z := by
      simpa using ((hasDerivAt_id z).const_mul 2).const_mul α
    have hq : HasDerivAt (fun z : ℝ => α * (2 * z) / (1 + z) ^ 2)
        ((α * 2 * (1 + z) ^ 2 - α * (2 * z) * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2) z :=
      hnum.div hden (pow_ne_zero 2 hz1)
    have hq3 := hq.div_const 3
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    simp only [Work.FM.Fstar]
    have hfun : (fun z : ℝ => α * (2 * z / (1 + z) ^ 2) / 3)
        = (fun z : ℝ => α * (2 * z) / (1 + z) ^ 2 / 3) := by
      funext u; ring
    rw [hfun]
    exact hq3.differentiableAt
  -- The primitive of `s ↦ s^{(5-α)/α} F_*(s)`, by the fundamental theorem of calculus.
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) z) z := by
    intro z hz
    have hzpos : 0 < z := hz
    have hq : 0 ≤ (5 - α) / α := by
      have h5 : (0 : ℝ) < 5 - α := by linarith
      positivity
    have hFon : ContinuousOn
        (fun s : ℝ => Work.Elliptic.Fstar (Work.Construction.Fstar α) s) (Set.Ioi (-1)) := by
      rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
      simp only [Work.FM.Fstar]
      apply ContinuousOn.div
      · apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro s hs
          exact pow_ne_zero 2 (by linarith [show (-1 : ℝ) < s from hs])
      · exact continuousOn_const
      · intro s hs; norm_num
    have hon : ContinuousOn (fun s : ℝ =>
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s) (Set.Ioi (-1)) :=
      (Real.continuous_rpow_const hq).continuousOn.mul hFon
    have hsub : Set.Icc (0 : ℝ) z ⊆ Set.Ioi (-1) := fun s hs => by
      simp only [Set.mem_Ioi]; linarith [hs.1, hzpos]
    have hInt : IntervalIntegrable (fun s : ℝ =>
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar (Work.Construction.Fstar α) s) volume 0 z := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le]
      exact ((hon.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    have hz1 : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    exact intervalIntegral.integral_hasDerivAt_right hInt
      (hon.stronglyMeasurableAtFilter isOpen_Ioi z hz1) (hon.continuousAt (isOpen_Ioi.mem_nhds hz1))
  intro z hz
  have hode := Work.Elliptic.Gsing_ode α (Work.Construction.Fstar α) hα hL12 hFc hJ z hz
  -- `(15/4) F_*(z) = (5α/4) φ(z)` for the profile.
  have hval : (15 / 4) * Work.Elliptic.Fstar (Work.Construction.Fstar α) z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z := by
    rw [Work.FTS.H2.PhiStarE.EllFstar_Fstar α hα hα1']
    rw [show Work.FTS.VocabO.phiR = Work.FM.Fstar from rfl]
    simp only [Work.FM.Fstar]
    ring
  -- `GzProfile = -Gsing`: the derivatives flip sign.
  have hd1 : deriv (GzProfile α) z
      = - deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z := by
    have h1 : GzProfile α = -(Work.Elliptic.Gsing α (Work.Construction.Fstar α)) := rfl
    rw [h1, deriv.neg]
  have h2 : iteratedDeriv 2 (GzProfile α) z
      = - iteratedDeriv 2 (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z := by
    change iteratedDeriv 2 (fun z => -(Work.Elliptic.Gsing α (Work.Construction.Fstar α) z)) z = _
    rw [iteratedDeriv_fun_neg]
  have h2b : iteratedDeriv 2 (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z
      = deriv (fun z' => deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h2b, hd1]
  rw [show -(α ^ 2 * z ^ 2 * (-(deriv (fun z' =>
            deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z)))
      - α * (5 + α) * z * (-(deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z))
      = α ^ 2 * z ^ 2 * deriv (fun z' =>
            deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α (Work.Construction.Fstar α)) z
      from by ring, hode, hval]

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.SlotsArith =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

/-- `HkNorm` is the square root of `HkSq`, so squaring inverts it. -/
theorem HkNorm_sq_eq (α : ℝ) (l : ℕ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm α l u ^ 2 = Work.Spaces.HkSq α l u := by
  rw [Work.Spaces.HkNorm]
  exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α l u)

/-- Squaring the bound `HkNorm u ≤ c · HkNorm v` (with `c ≥ 0`). -/
theorem HkSq_le_of_HkNorm_le (α : ℝ) {l : ℕ} {u v : ℝ → ℝ → ℝ} {c : ℝ} (_hc : 0 ≤ c)
    (h : Work.Spaces.HkNorm α l u ≤ c * Work.Spaces.HkNorm α l v) :
    Work.Spaces.HkSq α l u ≤ c ^ 2 * Work.Spaces.HkSq α l v := by
  have h1 : Work.Spaces.HkNorm α l u ^ 2 ≤ (c * Work.Spaces.HkNorm α l v) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [mul_pow, HkNorm_sq_eq, HkNorm_sq_eq] at h1
  exact h1

/-- On the open quadrant, the third slot of a difference is the `D_z` of the second slot of the
difference.  (`D_z = z ∂_z`; the two `∂_z`'s are applied to functions agreeing on the open
quadrant.) -/
theorem Dz_pthIter2_sub {u v : ℝ → ℝ → ℝ}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz (Work.Spaces.pthIter 2 u) z θ - Work.Spaces.Dz (Work.Spaces.pthIter 2 v) z θ
        = Work.Spaces.Dz (Work.Spaces.pthIter 2 (fun z θ => u z θ - v z θ)) z θ := by
  intro z θ hz hθ hθ2
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
  have h1 : Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 u z θ
        - Work.Spaces.pthIter 2 v z θ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
        - Work.Spaces.pz (Work.Spaces.pthIter 2 v) z θ := by
    simpa only [Function.uncurry, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
      using Work.FTS.GalBasis.pzIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 1
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hu 2).forall 2)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hv 2).forall 2) hpt
  have h2 : Work.Spaces.pz (fun z θ => Work.Spaces.pthIter 2 u z θ
        - Work.Spaces.pthIter 2 v z θ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 (fun z θ => u z θ - v z θ)) z θ := by
    refine Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ hpt
    intro p hp
    exact (Work.FTS.GalBasis.pthIter_sub_eqOn (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 2 (hu.forall 3) (hv.forall 3) hp).symm
  simp only [Work.Spaces.Dz]
  rw [← mul_sub, ← h1, h2]

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Model =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Boundary data and decay of the model part -/

/-- The model part vanishes at `θ = 0`. -/
theorem Model_zero {α : ℝ} {Gz ψ : ℝ → ℝ} {z : ℝ} (h : ψ 0 = 0) :
    Model α Gz ψ z 0 = 0 := by
  rw [Model]
  simp [h]

/-- The model part vanishes at `θ = π/2`. -/
theorem Model_pi_half {α : ℝ} {Gz ψ : ℝ → ℝ} {z : ℝ} (h : ψ (π / 2) = 0) :
    Model α Gz ψ z (π / 2) = 0 := by
  have h2 : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  rw [Model]
  simp [h, h2]

/-- The model part decays at `z → ∞` as soon as `Gz → 0` and `ψ` is bounded. -/
theorem Model_tendsto {α : ℝ} {Gz ψ : ℝ → ℝ} {C : ℝ}
    (hGz : Tendsto Gz atTop (𝓝 0)) (hψ : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) (θ : ℝ) :
    Tendsto (fun z => Model α Gz ψ z θ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => Gz z * Real.sin (2 * θ)) atTop (𝓝 (0 * Real.sin (2 * θ))) :=
    hGz.mul_const _
  have h2 : Tendsto (fun z : ℝ => α * Work.FTS.VocabO.phiR z * ψ θ)
      atTop (𝓝 (α * 0 * ψ θ)) :=
    (tendsto_phiR_atTop.const_mul α).mul_const (ψ θ)
  have h3 := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at h3
  refine h3.congr' (Eventually.of_forall fun z => ?_)
  simp only [Model]

/-! ## The flat expansion of `Φ̃_*` -/

/-- `Φ̃_* = Φ_* − Θ` in the flat coordinates: with `Φ_* = Model α GzProfile ψ + R`,
one has `Φ̃_*(z,θ) = Aprof α z · sin 2θ + α φ(z) ψ(θ) + R(z,θ)` for `z ≥ 0`. -/
theorem PhiTil_expansion_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ψ : ℝ → ℝ) (R : Fn)
    (z θ : ℝ) (hz : 0 ≤ z) :
    Work.Construction.PhiTil α (Work.Construction.Fstar α)
        (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) z θ
      = PhiTilExpansion α ψ R z θ := by
  rw [Work.Construction.PhiTil, PhiTilExpansion, Model, Aprof,
    Theta_eq_thetaProfile hα hα1 hz θ]
  ring

/-! ## Assembly of `IsBslSol` -/

/-- **The equation of the decomposition.**  If the model part has `bslOp`-image
`F_* − α²(𝒜φ)ψ` (the telescoping identity `phiStar_remainder_source`) and the remainder solves
`bslOp R = α²(𝒜φ)ψ`, then `Φ_* = Model + R` solves `bslOp α Φ_* = F_*` on the open quadrant.

The differentiability hypotheses are those needed by `Work.Elliptic.bslOp_add`. -/
theorem bslOp_split_eq {α : ℝ} {Gz ψ : ℝ → ℝ} {R : Fn}
    (hmodel : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α (Model α Gz ψ) z θ
        = Work.Construction.Fstar α z θ - RemSource α ψ z θ)
    (hrem : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hC2M : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry (Model α Gz ψ)) (z, θ))
    (hC2R : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry R) (z, θ))
    (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (fun z θ => Model α Gz ψ z θ + R z θ) z θ
      = Work.Construction.Fstar α z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ, Real.pi_pos], hθ2⟩)
  rw [Work.Elliptic.bslOp_add α _ R z θ hcos (hC2M z θ hz hθ hθ2) (hC2R z θ hz hθ hθ2),
    hmodel z hz θ hθ hθ2, hrem z hz θ hθ hθ2]
  ring

/-- **`IsBslSol` of the decomposition.**  Given the model equation, the remainder's equation,
the Dirichlet data of `Model` and `R` at `θ = 0, π/2`, and the decay of `Gz`, of `φ` and of `R`,
the sum `Model α Gz ψ + R` is a solution of `bslOp α Φ = F_*` in the class `IsBslSol`. -/
theorem isBslSol_of_split {α : ℝ} {Gz ψ : ℝ → ℝ} {R : Fn} {C : ℝ}
    (hmodel : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α (Model α Gz ψ) z θ
        = Work.Construction.Fstar α z θ - RemSource α ψ z θ)
    (hrem : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hC2M : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry (Model α Gz ψ)) (z, θ))
    (hC2R : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (Function.uncurry R) (z, θ))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ (π / 2) = 0)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hGzdec : Tendsto Gz atTop (𝓝 0)) (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α Gz ψ z θ + R z θ) := by
  refine ⟨fun z hz θ hθ hθ2 => bslOp_split_eq hmodel hrem hC2M hC2R z θ hz hθ hθ2, ?_, ?_, ?_⟩
  · intro z
    show Model α Gz ψ z 0 + R z 0 = 0
    rw [Model_zero hψ0, hR0 z, add_zero]
  · intro z
    show Model α Gz ψ z (π / 2) + R z (π / 2) = 0
    rw [Model_pi_half hψ1, hR1 z, add_zero]
  · intro θ hθ
    have h := (Model_tendsto (α := α) (Gz := Gz) (ψ := ψ) hGzdec hψbd θ).add (hRdec θ hθ)
    rw [add_zero] at h
    simpa using h

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The elementary `Ψ_S` -/

/-- `Ψ_S(θ) = ∫_θ^{π/2} sin²t cos³t dt = 2/15 − sin³θ/3 + sin⁵θ/5`. -/
def PsiS (θ : ℝ) : ℝ := 2 / 15 - Real.sin θ ^ 3 / 3 + Real.sin θ ^ 5 / 5

lemma PsiS_zero : PsiS 0 = 2 / 15 := by simp [PsiS]

lemma PsiS_pi_div_two : PsiS (π / 2) = 0 := by
  simp only [PsiS, Real.sin_pi_div_two]
  norm_num

lemma hasDerivAt_PsiS (θ : ℝ) :
    HasDerivAt PsiS (-(Real.sin θ ^ 2 * Real.cos θ ^ 3)) θ := by
  have h3 : HasDerivAt (fun t : ℝ => Real.sin t ^ 3) (3 * Real.sin θ ^ 2 * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 3
    rw [show ((fun t : ℝ => Real.sin t) ^ 3) = fun t : ℝ => Real.sin t ^ 3 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have h5 : HasDerivAt (fun t : ℝ => Real.sin t ^ 5) (5 * Real.sin θ ^ 4 * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 5
    rw [show ((fun t : ℝ => Real.sin t) ^ 5) = fun t : ℝ => Real.sin t ^ 5 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have h3' : HasDerivAt (fun t : ℝ => Real.sin t ^ 3 / 3) (Real.sin θ ^ 2 * Real.cos θ) θ := by
    have hh := h3.div_const 3
    convert hh using 1
    ring
  have h5' : HasDerivAt (fun t : ℝ => Real.sin t ^ 5 / 5) (Real.sin θ ^ 4 * Real.cos θ) θ := by
    have hh := h5.div_const 5
    convert hh using 1
    ring
  have h := (h5'.sub h3').const_add (2 / 15)
  convert h using 1
  · funext t; simp only [PsiS, Pi.sub_apply]; ring
  · have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [show Real.cos θ ^ 3 = Real.cos θ * Real.cos θ ^ 2 from by ring, hc]
    ring

/-- **The fundamental integral of `Ψ_S`**: `∫_a^b sin²t cos³t dt = Ψ_S(a) − Ψ_S(b)`. -/
theorem integral_sin_sq_cos_cu (a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, Real.sin t ^ 2 * Real.cos t ^ 3 = PsiS a - PsiS b := by
  have hcont : ContinuousOn PsiS (Set.Icc a b) := by
    change ContinuousOn (fun θ : ℝ => 2 / 15 - Real.sin θ ^ 3 / 3 + Real.sin θ ^ 5 / 5)
      (Set.Icc a b)
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => -(Real.sin t ^ 2 * Real.cos t ^ 3))
      volume a b := (by fun_prop : Continuous fun t : ℝ =>
        -(Real.sin t ^ 2 * Real.cos t ^ 3)).intervalIntegrable _ _
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt PsiS (-(Real.sin x ^ 2 * Real.cos x ^ 3)) x :=
    fun x _ => hasDerivAt_PsiS x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- `Ψ_S(θ) = ∫_θ^{π/2} sin²t cos³t dt`. -/
theorem PsiS_eq_integral (θ : ℝ) (hθ : θ ≤ π / 2) :
    PsiS θ = ∫ t in θ..(π / 2), Real.sin t ^ 2 * Real.cos t ^ 3 := by
  rw [integral_sin_sq_cos_cu θ (π / 2) hθ, PsiS_pi_div_two, sub_zero]


/-! ## Smoothness of `Γ`, and the `L∞` bound for `Γ̄` -/

/-- `Γ(θ) = (sinθ cos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
  have hpos : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), 0 < Real.sin θ * Real.cos θ ^ 2 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsm : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hlog : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => Real.log (Real.sin θ * Real.cos θ ^ 2)) (Set.Ioo 0 (π / 2)) :=
    hsm.log (fun θ hθ => ne_of_gt (hpos θ hθ))
  have hexp : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => Real.exp ((α / 3) * Real.log (Real.sin θ * Real.cos θ ^ 2)))
      (Set.Ioo 0 (π / 2)) := (((contDiffOn_const (c := α / 3) (s := Set.Ioo 0 (π / 2)))).mul hlog).exp
  refine hexp.congr (fun θ hθ => ?_)
  rw [Work.Spaces.Gam, Real.rpow_def_of_pos (hpos θ hθ), mul_comm]

/-- `Γ̄` is bounded on `[0,π/2]` by `1/c + 5/4`. -/
lemma abs_GamBar_le (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    |Work.FTS.VocabO.GamBar α θ| ≤ 1 / Work.Spaces.c α + 5 / 4 := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hG1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [Work.FTS.VocabO.GamBar]
  have hsplit : |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
      ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |(5:ℝ) / 4 * Real.sin (2 * θ)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (Work.Spaces.Gam α θ / Work.Spaces.c α) (-((5:ℝ) / 4 * Real.sin (2 * θ)))
  have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 1 / Work.Spaces.c α := by
    rw [abs_div, abs_of_pos hcpos, div_le_div_iff_of_pos_right hcpos, abs_of_nonneg hG0]
    exact hG1
  have h2 : |(5:ℝ) / 4 * Real.sin (2 * θ)| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5 / 4)]
    have := Real.abs_sin_le_one (2 * θ)
    linarith
  linarith

/-! ## Continuity of the source integrands on the angular interval -/

/-- Pointwise `rpow` identity for the `Γ`-integrand on the angular interval. -/
lemma sin_cos_sq_Gam_eq (α t : ℝ) (hα : 0 ≤ α) (h0 : 0 ≤ Real.sin t * Real.cos t ^ 2) :
    Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t
      = (Real.sin t * Real.cos t ^ 2) ^ (1 + α / 3) := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, Work.Spaces.Gam, Real.zero_rpow (by linarith : (1:ℝ) + α/3 ≠ 0), zero_mul]
  · rw [Work.Spaces.Gam]
    conv_rhs => rw [Real.rpow_add h 1 (α / 3)]
    rw [Real.rpow_one]

/-- On the closed angular interval the integrand `S C² Γ` is continuous (for `α ≥ 0`). -/
lemma continuousOn_sin_cos_sq_Gam (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
      (Set.Icc 0 (π / 2)) := by
  have hbase : ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (1 + α / 3))
      (Set.Icc 0 (π / 2)) :=
    ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).rpow_const
      (fun t _ => Or.inr (by positivity))
  refine hbase.congr (fun t ht => ?_)
  have h1 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_mem_Icc ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  exact sin_cos_sq_Gam_eq α t hα (mul_nonneg h1 (by positivity))

/-- On the closed angular interval the source integrand `S C² Γ̄` is continuous (for `α ≥ 0`). -/
lemma continuousOn_sin_cos_sq_GamBar (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      (Set.Icc 0 (π / 2)) := by
  have h1 := continuousOn_sin_cos_sq_Gam α hα
  have h2 : ContinuousOn (fun t : ℝ =>
      (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3)) (Set.Icc 0 (π / 2)) := by fun_prop
  refine ((h1.div_const (Work.Spaces.c α)).sub h2).congr (fun t _ => ?_)
  simp only [Work.FTS.VocabO.GamBar, Real.sin_two_mul, Pi.sub_apply]
  ring

/-- Interval-integrability of the source integrand on any subinterval of `[0,π/2]`. -/
lemma intervalIntegrable_GamBar (α : ℝ) (hα : 0 ≤ α) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ π / 2) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      volume a b := by
  have hsub : Set.uIcc a b ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  exact ((continuousOn_sin_cos_sq_GamBar α hα).mono hsub).intervalIntegrable

/-! ## The `Γ`-part `Ψ_Γ` of the source integral -/

/-- `Ψ_Γ(α,θ) = ∫_θ^{π/2} sin t cos²t Γ(α,t) dt`. -/
def PsiG (α θ : ℝ) : ℝ := ∫ t in θ..(π / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t




/-! ## The source integral `G₀` and its decomposition -/

/-- `G₀(α,θ) = ∫_θ^{π/2} sin t cos²t Γ̄(α,t) dt`. -/
def Gzero (α θ : ℝ) : ℝ := ∫ t in θ..(π / 2),
  Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t

lemma Gzero_pi_div_two (α : ℝ) : Gzero α (π / 2) = 0 := by simp [Gzero]

/-- `G₀(0) = 0`, the solvability (moment) condition of the angular model. -/
theorem Gzero_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) : Gzero α 0 = 0 := by
  have hmom := GamBar_moment (α := α) hα (by linarith)
  simp only [Work.Spaces.Iθ, Work.Elliptic.sinCos2] at hmom
  rw [Gzero, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  simpa only [mul_comm] using hmom

/-- **The decomposition of the source integral**: `G₀ = (1/c) Ψ_Γ − (5/2) Ψ_S`. -/
theorem Gzero_eq (α θ : ℝ) (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ : θ ≤ π / 2) :
    Gzero α θ = (1 / Work.Spaces.c α) * PsiG α θ - (5 / 2) * PsiS θ := by
  have h1 : IntervalIntegrable (fun t : ℝ =>
      (1 / Work.Spaces.c α) * (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t))
      volume θ (π / 2) :=
    (((continuousOn_sin_cos_sq_Gam α hα).const_mul _).mono (by
      intro t ht
      rw [Set.uIcc_of_le hθ] at ht
      exact ⟨le_trans hθ0 ht.1, ht.2⟩)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t : ℝ =>
      (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3)) volume θ (π / 2) :=
    (by fun_prop : Continuous fun t : ℝ =>
      (5 / 2 : ℝ) * (Real.sin t ^ 2 * Real.cos t ^ 3)).intervalIntegrable _ _
  have hpt : ∀ t : ℝ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t
      = (1 / Work.Spaces.c α) * (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
        - (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    intro t
    rw [Work.FTS.VocabO.GamBar, Real.sin_two_mul]
    ring
  rw [Gzero, intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, PsiG, ← PsiS_eq_integral θ hθ]

/-- **The derivative of `G₀`**: `G₀' = − sin θ cos²θ Γ̄`. -/
theorem hasDerivAt_Gzero (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Gzero α) (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) θ := by
  have hIcc := continuousOn_sin_cos_sq_GamBar α hα
  have hIoo : ContinuousOn (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) (Set.Ioo 0 (π / 2)) :=
    hIcc.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hsub : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le (le_of_lt hθ.2)] at ht
    exact ⟨le_trans (le_of_lt hθ.1) ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
    (hIcc.mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) (𝓝 θ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hIoo θ hθ
  have hcat : ContinuousAt (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) θ :=
    hIcc.continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  exact intervalIntegral.integral_hasDerivAt_left hint hmeas hcat

/-- `G₀` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_Gzero (α : ℝ) (hα : 0 ≤ α) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Gzero α) (Set.Ioo 0 (π / 2)) := by
  have hSC : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hsm : ContDiffOn ℝ (∞ : ℕ∞ω)
      (fun θ : ℝ => -(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ))
      (Set.Ioo 0 (π / 2)) := by
    have hG : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Work.FTS.VocabO.GamBar α θ)
        (Set.Ioo 0 (π / 2)) :=
      ((contDiffOn_Gam α).div_const (Work.Spaces.c α)).sub (by fun_prop)
    exact (hSC.mul hG).neg
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨fun θ hθ => (hasDerivAt_Gzero α hα hθ).differentiableAt.differentiableWithinAt,
    hsm.congr (fun θ hθ => (hasDerivAt_Gzero α hα hθ).deriv)⟩

/-- `G₀(θ) = −∫_0^θ sin t cos²t Γ̄`, using the vanishing `G₀(0) = 0`. -/
theorem Gzero_eq_neg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    Gzero α θ = -∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume 0 θ :=
    intervalIntegrable_GamBar α (le_of_lt hα) le_rfl hθ.2 hθ.1
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
    intervalIntegrable_GamBar α (le_of_lt hα) hθ.1 le_rfl hθ.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have h0 := Gzero_zero α hα hα1
  simp only [Gzero] at h0 ⊢
  linarith [hadd]

/-- The pointwise bound `|S C² Γ̄| ≤ 13t` on `[0,1]`. -/
lemma abs_sin_cos_sq_GamBar_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| ≤ 13 * t := by
  have htπ : t ≤ π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : t ∈ Set.Icc (0:ℝ) (π / 2) := ⟨ht0, htπ⟩
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc10 : 1 / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]; linarith
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht0, by linarith [Real.pi_pos]⟩
  have hcos : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht0, Real.pi_pos], htπ⟩
  have hG1 := (Work.Spaces.Gam_bounds α t hα hmem).2
  have hG0 := (Work.Spaces.Gam_bounds α t hα hmem).1
  have hsinle : Real.sin t ≤ t := Real.sin_le ht0
  have hsin2b : |Real.sin (2 * t)| ≤ 2 * t := by
    have h := Real.abs_sin_le_abs (x := 2 * t)
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)] at h
  have hcos2 : Real.cos t ^ 2 ≤ 1 := by nlinarith [Real.cos_sq_le_one t]
  have hSC1 : Real.sin t * Real.cos t ^ 2 ≤ t := by nlinarith [hsinle, hcos2, hsin]
  have hSC0 : 0 ≤ Real.sin t * Real.cos t ^ 2 := mul_nonneg hsin (by positivity)
  have hGb : |Work.FTS.VocabO.GamBar α t| ≤ 10 + (5 / 2) * t := by
    rw [Work.FTS.VocabO.GamBar]
    have hsplit : |Work.Spaces.Gam α t / Work.Spaces.c α - 5 / 4 * Real.sin (2 * t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5:ℝ) / 4 * Real.sin (2 * t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α) (-((5:ℝ) / 4 * Real.sin (2 * t)))
    have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α| ≤ 10 := by
      rw [abs_of_nonneg (div_nonneg hG0 (le_of_lt hcpos))]
      calc Work.Spaces.Gam α t / Work.Spaces.c α ≤ 1 / Work.Spaces.c α :=
            div_le_div_of_nonneg_right hG1 (le_of_lt hcpos)
        _ ≤ 10 := hc10
    have h2 : |(5:ℝ) / 4 * Real.sin (2 * t)| ≤ (5 / 2) * t := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5 / 4)]
      linarith [hsin2b]
    linarith
  rw [abs_mul, abs_of_nonneg hSC0]
  have hfin : Real.sin t * Real.cos t ^ 2 * |Work.FTS.VocabO.GamBar α t|
      ≤ t * (10 + (5 / 2) * t) := mul_le_mul hSC1 hGb (abs_nonneg _) ht0
  nlinarith [hfin, ht0, ht1]

/-- Near `0`: `|G₀(θ)| ≤ 7θ²` for `θ ∈ [0,1]`. -/
theorem Gzero_abs_le_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : |Gzero α θ| ≤ 7 * θ ^ 2 := by
  have hθπ : θ ≤ π / 2 := by have := Real.pi_gt_three; linarith
  have hmem : θ ∈ Set.Icc (0:ℝ) (π / 2) := ⟨hθ0, hθπ⟩
  rw [Gzero_eq_neg α hα hα1 θ hmem, abs_neg]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (f := fun t : ℝ =>
    Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) hθ0) ?_
  have hsub : Set.uIcc (0:ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hθ0] at ht
    exact ⟨ht.1, le_trans ht.2 hθπ⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|) volume 0 θ :=
    (((continuousOn_sin_cos_sq_GamBar α (le_of_lt hα)).mono hsub).abs).intervalIntegrable
  have hint2 : IntervalIntegrable (fun t : ℝ => 13 * t) volume 0 θ :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hmono : (∫ t in 0..θ, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|)
      ≤ ∫ t in 0..θ, (13 * t) :=
    intervalIntegral.integral_mono_on hθ0 hint hint2 (fun t ht =>
      abs_sin_cos_sq_GamBar_le α hα (by linarith) ht.1 (le_trans ht.2 hθ1))
  have hval : (∫ t in 0..θ, (13 * t)) = 13 * θ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  linarith [hmono, hval, sq_nonneg θ]

/-- The elementary `L∞` bound for `G₀`: `|G₀(θ)| ≤ (1/c + 5/4)(π/2−θ) cos²θ`. -/
theorem Gzero_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    |Gzero α θ| ≤ (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := by
  have hδ0 : 0 ≤ π / 2 - θ := by linarith [hθ.2]
  have hCpos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [Gzero]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hθ.2) ?_
  have hsub : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
    intro t ht
    rw [Set.uIcc_of_le hθ.2] at ht
    exact ⟨le_trans hθ.1 ht.1, ht.2⟩
  have hint : IntervalIntegrable (fun t : ℝ =>
      |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|) volume θ (π / 2) :=
    (((continuousOn_sin_cos_sq_GamBar α (le_of_lt hα)).mono hsub).abs).intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => Real.cos θ ^ 2 *
      (1 / Work.Spaces.c α + 5 / 4)) volume θ (π / 2) := continuous_const.intervalIntegrable _ _
  have hm : (∫ t in θ..(π / 2), |Real.sin t * Real.cos t ^ 2 *
      Work.FTS.VocabO.GamBar α t|)
      ≤ ∫ t in θ..(π / 2), Real.cos θ ^ 2 * (1 / Work.Spaces.c α + 5 / 4) := by
    refine intervalIntegral.integral_mono_on hθ.2 hint hint2 ?_
    intro t ht
    have htmem : t ∈ Set.Icc (0:ℝ) (π / 2) := ⟨le_trans hθ.1 ht.1, ht.2⟩
    have h1 : 0 ≤ Real.sin t := by
      have h0t : 0 ≤ t := le_trans hθ.1 ht.1
      have htπ' : t ≤ π := by linarith [ht.2, Real.pi_gt_three]
      exact Real.sin_nonneg_of_mem_Icc ⟨h0t, htπ'⟩
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, ht.1, Real.pi_pos], ht.2⟩
    have h2 : Real.cos t ^ 2 ≤ Real.cos θ ^ 2 := by
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
        (by linarith [ht.2, Real.pi_gt_three]) ht.1
      nlinarith [hcos, hCpos]
    have h3 : |Work.FTS.VocabO.GamBar α t| ≤ 1 / Work.Spaces.c α + 5 / 4 :=
      abs_GamBar_le α t hα hα1 htmem
    have h4 : Real.sin t * Real.cos t ^ 2 ≤ Real.cos θ ^ 2 := by
      nlinarith [Real.sin_le_one t, hcos]
    rw [abs_mul, abs_of_nonneg (mul_nonneg h1 (by positivity))]
    exact mul_le_mul h4 h3 (abs_nonneg _) (sq_nonneg _)
  have hval : (∫ t in θ..(π / 2), Real.cos θ ^ 2 * (1 / Work.Spaces.c α + 5 / 4))
      = (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    ring
  linarith [hm, hval]

/-! ## `P = G₀/(2C³)`, its derivative and its elementary bounds -/

/-- `P(α,θ) = G₀(α,θ)/(2 cos³θ)`, the profile of `w' = P/sin²θ`. -/
def Pfun (α θ : ℝ) : ℝ := Gzero α θ / (2 * Real.cos θ ^ 3)

/-- **The derivative of `P`**: `P' = − S Γ̄/(2C) + 3 S P/C`. -/
theorem hasDerivAt_Pfun (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Pfun α)
      (-(Real.sin θ * Work.FTS.VocabO.GamBar α θ / (2 * Real.cos θ))
        + 3 * Real.sin θ * Pfun α θ / Real.cos θ) θ := by
  have hCpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.cos t ^ 3)
      (-(6 * Real.sin θ * Real.cos θ ^ 2)) θ := by
    have h3 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos θ ^ 2 * (-Real.sin θ)) θ := by
      have h := (Real.hasDerivAt_cos θ).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = fun t : ℝ => Real.cos t ^ 3 from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have hh := h3.const_mul (2 : ℝ)
    convert hh using 1
    ring
  have hnum : HasDerivAt (Gzero α)
      (-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ)) θ :=
    hasDerivAt_Gzero α hα hθ
  have hquot := hnum.div hden (by positivity)
  have hgoal : HasDerivAt (fun t : ℝ => Pfun α t)
      ((-(Real.sin θ * Real.cos θ ^ 2 * Work.FTS.VocabO.GamBar α θ) * (2 * Real.cos θ ^ 3)
        - Gzero α θ * -(6 * Real.sin θ * Real.cos θ ^ 2)) / (2 * Real.cos θ ^ 3) ^ 2) θ := hquot
  convert hgoal using 1
  rw [Pfun]
  field_simp
  ring

lemma contDiffOn_Pfun (α : ℝ) (hα : 0 ≤ α) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Pfun α) (Set.Ioo 0 (π / 2)) := by
  have hcos : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => 2 * Real.cos θ ^ 3) (Set.Ioo 0 (π/2)) := by
    fun_prop
  exact (contDiffOn_Gzero α hα).div hcos (fun θ hθ => by
    have hCpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity)

/-- `|P(θ)| ≤ 20` on `[0,π/2]`. -/
theorem Pfun_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |Pfun α θ| ≤ 20 := by
  rcases eq_or_lt_of_le hθ.2 with hπ | hπ
  · rw [hπ, Pfun, Gzero_pi_div_two]
    simp [Real.cos_pi_div_two]
  · have hCpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hπ⟩
    have hδ0 : 0 ≤ π / 2 - θ := by linarith
    have hG := Gzero_abs_le α hα (by linarith) hθ
    have hcp : 1 / Work.Spaces.c α + 5 / 4 ≤ 12 := by
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have h10 : 1 / Work.Spaces.c α ≤ 10 := by
        have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 / 10) hc
        have h2 : (1:ℝ) / (1 / 10) = 10 := by norm_num
        rwa [h2] at h
      linarith
    have hδ : π / 2 - θ ≤ (π / 2) * Real.cos θ := by
      have hsin : Real.cos θ = Real.sin (π / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
      have hh : (2 / π) * (π / 2 - θ) ≤ Real.sin (π / 2 - θ) :=
        Real.mul_le_sin hδ0 (by linarith [hθ.1, hπ, Real.pi_pos])
      rw [hsin]
      have hπ2 : (0:ℝ) < π / 2 := by positivity
      have h3 : (π / 2) * ((2 / π) * (π / 2 - θ)) ≤ (π / 2) * Real.sin (π / 2 - θ) :=
        mul_le_mul_of_nonneg_left hh (le_of_lt hπ2)
      have h4 : (π / 2) * ((2 / π) * (π / 2 - θ)) = π / 2 - θ := by
        field_simp
      linarith [h3, h4]
    rw [Pfun, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3),
      div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3)]
    have hC2 : (0:ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
    calc |Gzero α θ| ≤ (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ) * Real.cos θ ^ 2 := hG
      _ ≤ 12 * ((π / 2) * Real.cos θ) * Real.cos θ ^ 2 := by
          have h1 : (1 / Work.Spaces.c α + 5 / 4) * (π / 2 - θ)
              ≤ 12 * ((π / 2) * Real.cos θ) :=
            mul_le_mul hcp hδ hδ0 (by positivity)
          exact mul_le_mul_of_nonneg_right h1 hC2
      _ = 6 * π * Real.cos θ ^ 3 := by ring
      _ ≤ 20 * (2 * Real.cos θ ^ 3) := by nlinarith [hCpos, Real.pi_lt_four, pow_pos hCpos 3]

/-- Near `0`: `|P(θ)| ≤ 30θ²` for `θ ∈ [0,1/2]`. -/
theorem Pfun_abs_le_sq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) : |Pfun α θ| ≤ 30 * θ ^ 2 := by
  have hC : (1 / 2 : ℝ) ≤ Real.cos θ := by
    have hπ : θ ≤ π / 3 := by have := Real.pi_gt_three; linarith
    have h1 : Real.cos (π / 3) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hπ
    rwa [Real.cos_pi_div_three] at h1
  have hC3 : (1 / 8 : ℝ) ≤ Real.cos θ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hC 3
    norm_num at h
    exact h
  rw [Pfun, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3),
    div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.cos θ ^ 3)]
  have hG := Gzero_abs_le_sq α hα hα1 hθ0 (by linarith)
  nlinarith [hG, hC3, sq_nonneg θ]

/-- `|P(θ)/sin²θ| ≤ 500` on `[0,π/2]`. -/
theorem Pfun_div_sin_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |Pfun α θ / Real.sin θ ^ 2| ≤ 500 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hbase : (0:ℝ) < 2 / π := by positivity
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp [Pfun]
  · have hsin0 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [hθ.2, Real.pi_pos])
    rcases le_or_gt θ (1 / 2) with h | h
    · have hsin : (2 / π) * θ ≤ Real.sin θ := Real.mul_le_sin hθ.1 hθ.2
      have hsinB0 : 0 ≤ (2 / π) * θ := mul_nonneg (le_of_lt hbase) hθ.1
      have hsq : ((2 / π) * θ) ^ 2 ≤ Real.sin θ ^ 2 :=
        pow_le_pow_left₀ hsinB0 hsin 2
      have hP := Pfun_abs_le_sq α hα hα1 hθ.1 h
      have h2 : 0 < ((2 / π) * θ) ^ 2 := by positivity
      have hkey : |Pfun α θ| / Real.sin θ ^ 2 ≤ 30 * θ ^ 2 / ((2 / π) * θ) ^ 2 :=
        div_le_div₀ (by positivity) hP h2 hsq
      have hv : 30 * θ ^ 2 / ((2 / π) * θ) ^ 2 = 30 / (2 / π) ^ 2 := by
        rw [mul_pow]
        field_simp
      rw [hv] at hkey
      have hge : (1 / 4 : ℝ) ≤ (2 / π) ^ 2 := by
        have h1 : (1 / 2 : ℝ) ≤ 2 / π := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < π)]
          linarith [Real.pi_lt_four]
        nlinarith [h1]
      have hb : 30 / (2 / π) ^ 2 ≤ 500 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (2 / π) ^ 2)]
        nlinarith [hge]
      linarith
    · have hsin : (2 / π) * (1 / 2 : ℝ) ≤ Real.sin θ := by
        have h1 : (2 / π) * (1 / 2 : ℝ) ≤ (2 / π) * θ := mul_le_mul_of_nonneg_left h.le
          (le_of_lt hbase)
        linarith [Real.mul_le_sin hθ.1 hθ.2]
      have hbase2 : (0:ℝ) ≤ (2 / π) * (1 / 2 : ℝ) :=
        mul_nonneg (le_of_lt hbase) (by norm_num)
      have hsq : ((2 / π) * (1 / 2 : ℝ)) ^ 2 ≤ Real.sin θ ^ 2 :=
        pow_le_pow_left₀ hbase2 hsin 2
      have hP := Pfun_abs_le α hα hα1 hθ
      have h2 : 0 < ((2 / π) * (1 / 2 : ℝ)) ^ 2 := by positivity
      have hkey : |Pfun α θ| / Real.sin θ ^ 2 ≤ 20 / ((2 / π) * (1 / 2 : ℝ)) ^ 2 :=
        div_le_div₀ (by positivity) hP h2 hsq
      have hge : (1 / 4 : ℝ) ≤ (2 / π) * (1 / 2 : ℝ) := by
        have h1 : (1 / 2 : ℝ) ≤ 2 / π := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < π)]
          linarith [Real.pi_lt_four]
        linarith
      have hb : 20 / ((2 / π) * (1 / 2 : ℝ)) ^ 2 ≤ 500 := by
        rw [div_le_iff₀ h2]
        nlinarith [hge]
      linarith

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.phiAPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

/-- **Small-`z` regime**: `|𝒜φ(α,z)| ≤ 20 z` for `0 < z ≤ 1`, `0 < α ≤ 1`. -/
theorem phiA_abs_le_small {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    |Work.FTS.VocabO.phiA α z| ≤ 20 * z := by
  have hz : z ≠ -1 := by linarith
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  have hpos4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hpos3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have h2mz : (0 : ℝ) ≤ 2 - z := by linarith
  have h1mz : (0 : ℝ) ≤ 1 - z := by linarith
  have h1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 8 * z := by
    rw [abs_div, abs_of_pos hpos4, div_le_iff₀ hpos4]
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * (2 - z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg hz2, abs_of_nonpos (by linarith : z - 2 ≤ 0)]
      ring
    rw [habs]
    have hkey : z * (2 - z) ≤ 2 * (1 + z) ^ 4 := by
      have hzz : z * (2 - z) ≤ 1 := by nlinarith [sq_nonneg (z - 1)]
      have h4 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
      linarith
    have hnn : (0 : ℝ) ≤ z ^ 2 * (2 - z) := mul_nonneg hz2 h2mz
    nlinarith [hkey, hnn, hα, hα1, hz0]
  have h2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 * z := by
    rw [abs_div, abs_of_pos hpos3, div_le_iff₀ hpos3]
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * (1 - z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz0.le, abs_of_nonneg h1mz]
    rw [habs]
    have h4 : (1 : ℝ) ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z)
    have hnn : (0 : ℝ) ≤ z * (1 - z) := mul_nonneg hz0.le h1mz
    have e1 : 2 * (5 + α) * z * (1 - z) ≤ 12 * z * (1 - z) := by
      have hc : 2 * (5 + α) ≤ 12 := by linarith
      have := mul_le_mul_of_nonneg_right hc hnn
      linarith [this]
    have e2 : 12 * z * (1 - z) ≤ 12 * z * (1 + z) ^ 3 := by
      have hle : (1 - z) ≤ (1 + z) ^ 3 := by linarith
      have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 12 * z)
      linarith [this]
    linarith [e1, e2]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| :=
        abs_add_le _ _
    _ ≤ 8 * z + 12 * z := by linarith
    _ = 20 * z := by ring

/-- **Large-`z` regime**: `|𝒜φ(α,z)| ≤ 24 / z` for `1 ≤ z`, `0 < α ≤ 1`. -/
theorem phiA_abs_le_large {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz1 : 1 ≤ z) :
    |Work.FTS.VocabO.phiA α z| ≤ 24 / z := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz : z ≠ -1 := by linarith
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  have hpos4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
  have hpos3 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hz4 : (0 : ℝ) < z ^ 4 := by positivity
  have h1 : |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| ≤ 12 / z := by
    have habs : |4 * α * z ^ 2 * (z - 2)| = 4 * α * z ^ 2 * |z - 2| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hα,
        abs_of_nonneg (sq_nonneg z)]
    have hle : |z - 2| ≤ z + 2 := by rw [abs_le]; constructor <;> linarith
    have hA : 4 * α * z ^ 2 * |z - 2| ≤ 4 * z ^ 2 * (z + 2) := by
      have hnn : (0 : ℝ) ≤ z ^ 2 * |z - 2| := mul_nonneg (sq_nonneg z) (abs_nonneg _)
      have h2 : 4 * α * (z ^ 2 * |z - 2|) ≤ 4 * 1 * (z ^ 2 * (z + 2)) := by
        have hab : z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left hle (sq_nonneg z)
        nlinarith [hab, hnn, hα, hα1]
      linarith [h2]
    have hB : 4 * z ^ 2 * (z + 2) ≤ 12 * z ^ 3 := by nlinarith [hz1]
    have hD : z ^ 4 ≤ (1 + z) ^ 4 := by nlinarith [hz0]
    rw [abs_div, abs_of_pos hpos4, habs]
    have hstep1 : 4 * α * z ^ 2 * |z - 2| / (1 + z) ^ 4 ≤ 12 * z ^ 3 / (1 + z) ^ 4 :=
      div_le_div_of_nonneg_right (by linarith) hpos4.le
    have hstep2 : 12 * z ^ 3 / (1 + z) ^ 4 ≤ 12 * z ^ 3 / z ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) hz4 hD
    have hstep3 : 12 * z ^ 3 / z ^ 4 = 12 / z := by field_simp
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  have h2 : |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| ≤ 12 / z := by
    have habs : |2 * (5 + α) * z * (1 - z)| = 2 * (5 + α) * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : (0 : ℝ) < 5 + α), abs_of_nonneg hz0.le]
    have hle : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
    have hA : 2 * (5 + α) * z * |1 - z| ≤ 12 * z * (1 + z) := by
      have hab : z * |1 - z| ≤ z * (1 + z) := mul_le_mul_of_nonneg_left hle hz0.le
      have hnn : (0 : ℝ) ≤ z * |1 - z| := mul_nonneg hz0.le (abs_nonneg _)
      have h2 : 2 * (5 + α) * (z * |1 - z|) ≤ 12 * (z * (1 + z)) := by
        have hc : 2 * (5 + α) ≤ 12 := by linarith
        nlinarith [hab, hnn, hc]
      linarith [h2]
    rw [abs_div, abs_of_pos hpos3, habs]
    have hstep1 : 2 * (5 + α) * z * |1 - z| / (1 + z) ^ 3 ≤ 12 * z * (1 + z) / (1 + z) ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) hpos3.le
    have hstep2 : 12 * z * (1 + z) / (1 + z) ^ 3 ≤ 12 * z / z ^ 2 := by
      have he : 12 * z * (1 + z) / (1 + z) ^ 3 = 12 * z / (1 + z) ^ 2 := by field_simp
      rw [he]
      exact div_le_div_of_nonneg_left (by positivity) hz2 (by nlinarith [hz0])
    have hstep3 : 12 * z / z ^ 2 = 12 / z := by field_simp
    linarith [hstep1, hstep2, hstep3.le, hstep3.ge]
  calc |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3|
      ≤ |4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4| + |2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3| :=
        abs_add_le _ _
    _ ≤ 12 / z + 12 / z := by linarith
    _ = 24 / z := by ring

end Work.FTS.PhiStar.Series.Deleg
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.phiAeqSeries =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- `phiAseries α 0` is the four-term partial-fraction expression of `𝒜φ`. -/
lemma phiAseries_zero (α z : ℝ) :
    phiAseries α 0 z = (2 * α - 10) / (1 + z) + (30 - 14 * α) / (1 + z) ^ 2
      + (24 * α - 20) / (1 + z) ^ 3 + (-12 * α) / (1 + z) ^ 4 := by
  simp only [phiAseries, Finset.prod_range_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    phiAcoef, mul_one]
  norm_num
  field_simp

/-- The explicit rational form of `phiA` (`Work.FTS.PhiStar.phiA_eq`) reassociated as a
sum of the four powers of `1/(1+z)`. -/
lemma phiA_rational_eq (α z : ℝ) :
    4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3
      = (2 * α - 10) / (1 + z) + (30 - 14 * α) / (1 + z) ^ 2
        + (24 * α - 20) / (1 + z) ^ 3 + (-12 * α) / (1 + z) ^ 4 := by
  field_simp
  ring

theorem phiAeqSeries (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z = Work.FTS.PhiStar.Series.Deleg.phiAseries α 0 z := by
  rw [phiAseries_zero, ← phiA_rational_eq, Work.FTS.PhiStar.phiA_eq α z hz]

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.phiA_abs_le_inv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

/-- The explicit rational form of `𝒜φ = phiA α z` combined over the common denominator
`(1+z)^4` (from `Work.FTS.PhiStar.phiA_eq`). -/
theorem phiA_combined (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z
      = ((2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z) / (1 + z) ^ 4 := by
  rw [Work.FTS.PhiStar.phiA_eq α z hz]
  field_simp
  ring


end Work.FTS.PhiStar.Series
end
-- ===== merged: Submission.Work.FTS.PhiStar.bslOp_sol_exists =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.bslOp_sol_exists_pp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.bslOp_sol_exists_pp` — the repaired elliptic existence node (two orders of slack)

Lead install, 2026-10-11 (`cbc/fts_phistar_REVIEW.md`, `cbc/fts_mem10_install.md`).

The original node `PhiStar.bslOp_sol_exists k` (`HkMem α k F ⇒ EllWeakPos α k`) is **false** at
every `k`, in particular at `k = 8`: `EllWeakPos α k` contains the order-`k+3` slot
`HkMem α k (z∂_z∂_θ²Ψ)`, while `bslOp` is uniformly elliptic with `s = log z`-invariant
coefficients in interior windows, so `F ∈ ℋᵏ` only gives order `k+2` for `Ψ` (review §1–§2,
explicit counterexample with disjoint bumps at `s_n = 10n`).  One extra order is not enough
either: the every-`z` slice conjunct of `HkMem` fails at top order (review §3).

The repaired node assumes `HkMem α (k+2) F`.  It is used at `k = 8` (ClassC field `mem10`), via
`EllExist.ellClassOk_exists_of_inputs_pp 8` in `ClassC.A2`.  The old file is left untouched
(it is no longer on the `theorem_1_v2` path).
-/

namespace Work.FTS.PhiStar


end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.const_le_of_moment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `sin θ ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin θ := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sinθ cos²θ ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (sin_nonneg_of_mem_Iθ hθ) (sq_nonneg _)

theorem const_le_of_moment {v w : ℝ → ℝ} {c M : ℝ}
    (hvw : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), v θ = w θ + c)
    (hw : ∀ θ ∈ Work.Spaces.Iθ, |w θ| ≤ M)
    (hwmeas : MeasureTheory.AEStronglyMeasurable w (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmom : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * v θ * Work.Elliptic.sinCos2 θ = 0) :
    |c| ≤ M := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- `M` is nonnegative: apply the bound to any point of `Iθ`.
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (w 0)) (hw 0 Work.Spaces.zero_mem_Iθ)
  -- The weight `g θ = sin 2θ · sinθcos²θ` is nonnegative and bounded by `1` on `Iθ`.
  have hg_nonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
    fun θ hθ => mul_nonneg (sin_two_nonneg_of_mem_Iθ hθ) (sinCos2_nonneg_of_mem_Iθ hθ)
  have hg_abs_le_one : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| ≤ 1 := by
    intro θ hθ
    have hsc_le : Work.Elliptic.sinCos2 θ ≤ 1 := by
      rw [Work.Elliptic.sinCos2]
      nlinarith [Real.sin_le_one θ, Real.cos_sq_le_one θ, sin_nonneg_of_mem_Iθ hθ,
        sq_nonneg (Real.cos θ)]
    have hmul : Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ ≤ 1 := by
      have := mul_le_mul (Real.sin_le_one (2 * θ)) hsc_le (sinCos2_nonneg_of_mem_Iθ hθ)
        zero_le_one
      simpa using this
    rw [abs_le]
    exact ⟨by linarith [hg_nonneg θ hθ], hmul⟩
  have hg_cont : Continuous (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    rw [show (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        = (fun θ : ℝ => Real.sin (2 * θ) * (Real.sin θ * Real.cos θ ^ 2)) from rfl]
    fun_prop
  -- Integrability of the two pieces of the split.
  have hgw_int : Integrable (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.of_bound (hg_cont.aestronglyMeasurable.mul hwmeas) M ?_
    filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| * |w θ|
        ≤ 1 * M := mul_le_mul (hg_abs_le_one θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hcg_int : Integrable (fun θ : ℝ => c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) :=
    ((continuous_const.mul hg_cont).continuousOn).integrableOn_compact isCompact_Icc
  -- The moment splits as `∫ g·w + c·∫ g`.
  have hkey : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ
      = (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
        + c * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    have h1 : (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ)
        =ᵐ[volume.restrict (Set.Ioo (0:ℝ) (π / 2))]
        (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ
          + c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hvw θ hθ]; ring
    have h2 : (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ
          + c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) :=
      (MeasureTheory.ae_restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := π / 2))).mp h1
    rw [integral_congr_ae h2, integral_add hgw_int hcg_int, integral_const_mul]
  have h0 : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ = 0 := by
    rw [← hmom]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hkey2 : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
      + c * (4 / 15) = 0 := by
    have h := hkey
    rw [h0, Work.Elliptic.integral_sin_two_mul_sinCos2] at h
    exact h.symm
  have hc_eq : c
      = -(15 / 4) * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ) := by
    linarith [hkey2]
  -- Bound the remaining moment by `M · ∫ g`.
  have hA : |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
      ≤ M * (4 / 15) := by
    have hgwabs_int : Integrable (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Integrable.of_bound (hg_cont.aestronglyMeasurable.mul hwmeas.norm) M ?_
      filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      calc |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| * |w θ|
          ≤ 1 * M := mul_le_mul (hg_abs_le_one θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hbound : ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖
        = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ| := by
      refine setIntegral_congr_fun hIθ_meas (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nonneg θ hθ)]
    have hmono : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ|
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * M := by
      refine setIntegral_mono_on hgwabs_int ?_ hIθ_meas (fun θ hθ => ?_)
      · exact ((hg_cont.mul continuous_const).continuousOn).integrableOn_compact isCompact_Icc
      · exact mul_le_mul_of_nonneg_left (hw θ hθ) (hg_nonneg θ hθ)
    have hstep : |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    calc |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖ := hstep
      _ = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ| := hbound
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * M := hmono
      _ = M * (4 / 15) := by
          rw [integral_mul_const, Work.Elliptic.integral_sin_two_mul_sinCos2]
          ring
  have hfin : |c| ≤ 15 / 4 * (M * (4 / 15)) := by
    rw [hc_eq, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 15 / 4)]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  linarith [hfin]

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.phiStar_remainder_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.PhiStar

/-- **The telescoping identity `P2` of the `Φ_*` node.**

With `φ = phiR = 2z/(1+z)²`, `𝒜φ = phiA = αz²φ'' + (5+α)zφ'`, `Γ̄ = GamBar = Γ/c − (5/4)sin 2θ`,
`ψ` solving `L₀ψ = Γ̄` in the interior, and `Gz` solving the radial model
`−(α²z²Gz'') − α(5+α)zGz' = (5α/4)φ`,

`bslOp α (Gz·sin 2θ + α·φ·ψ) = F_* − α²·(𝒜φ)·ψ`  on the open quadrant.

Proof: `bslOp` is additive (`bslOp_add`), the first piece is a radial multiple of `sin 2θ`
(`bslOp_radial` + the model equation for `Gz`) and contributes `(5α/4)φ sin 2θ`, the second is a
separable product (`bslOp_sep`) and contributes `α φ (Γ̄ + (5/4)sin 2θ) − α²(𝒜φ)ψ`.  The
`(5α/4)φ sin 2θ` terms cancel and `Γ̄ + (5/4)sin 2θ = Γ/c`, which gives `F_* = α(Γ/c)φ`. -/
theorem phiStar_remainder_source (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ) (Gz : ℝ → ℝ)
    (hψ : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (π / 2)))
    (hψeq : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ)
    (hG : ∀ z, 0 < z → -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z) - α * (5 + α) * z * deriv Gz z
        = (5 * α / 4) * Work.FTS.VocabO.phiR z)
    (hGd : ContDiffOn ℝ 2 Gz (Set.Ioi 0)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α
        (fun z' θ' => Gz z' * Real.sin (2 * θ') + α * Work.FTS.VocabO.phiR z' * ψ θ') z θ
      = Work.Construction.Fstar α z θ - α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ := by
  intro z hz θ hθ0 hθ1
  have hmem : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, hθ1⟩)
    linarith [Real.pi_pos]
  -- `phiR` is `C²` at `z > 0` (`2z/(1+z)²` is a quotient with nonvanishing denominator there)
  have hphi : ContDiffAt ℝ 2 Work.FTS.VocabO.phiR z := by
    change ContDiffAt ℝ 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) z
    exact ContDiffAt.div ((contDiffAt_const (c := (2 : ℝ))).mul contDiffAt_id)
      ((contDiffAt_const.add contDiffAt_id).pow 2)
      (by have h1z : (1 + z) ≠ 0 := by intro h; linarith [hz]
          exact pow_ne_zero 2 h1z)
  -- joint `C²` regularity of the two summands, as required by `bslOp_add`
  have hCd1 : ContDiffAt ℝ 2
      (Function.uncurry (fun z' θ' => Gz z' * Real.sin (2 * θ'))) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 Gz z := hGd.contDiffAt (isOpen_Ioi.mem_nhds hz)
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Gz p.1) (z, θ) := by
      simpa [Function.comp_def] using h1.comp (z, θ) (contDiffAt_fst (p := (z, θ)))
    have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by
      have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => 2 * p.2) (z, θ) := by
        simpa [Function.comp_def] using
          (contDiffAt_const (c := (2 : ℝ))).mul (contDiffAt_snd (p := (z, θ)))
      simpa [Function.comp_def] using (Real.contDiff_sin.contDiffAt).comp (z, θ) h2
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Gz p.1 * Real.sin (2 * p.2)) (z, θ)
    exact hfst.mul hsnd
  have hCd2 : ContDiffAt ℝ 2
      (Function.uncurry (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ')) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (fun z' => α * Work.FTS.VocabO.phiR z') z :=
      (contDiffAt_const (c := α)).mul hphi
    have h2 : ContDiffAt ℝ 2 ψ θ := hψ.contDiffAt (isOpen_Ioo.mem_nhds hmem)
    have hfst : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1) (z, θ) := by
      simpa [Function.comp_def] using h1.comp (z, θ) (contDiffAt_fst (p := (z, θ)))
    have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.2) (z, θ) := by
      simpa [Function.comp_def] using h2.comp (z, θ) (contDiffAt_snd (p := (z, θ)))
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => α * Work.FTS.VocabO.phiR p.1 * ψ p.2) (z, θ)
    exact hfst.mul hsnd
  -- the radial piece: `bslOp α (Gz · sin 2θ) = (5α/4)φ · sin 2θ`
  have hrad : Work.Elliptic.bslOp α (fun z' θ' => Gz z' * Real.sin (2 * θ')) z θ
      = (5 * α / 4) * Work.FTS.VocabO.phiR z * Real.sin (2 * θ) := by
    rw [bslOp_radial α Gz z θ hcos,
      show -(α ^ 2 * z ^ 2 * iteratedDeriv 2 Gz z + α * (5 + α) * z * deriv Gz z)
        = (5 * α / 4) * Work.FTS.VocabO.phiR z by linarith [hG z hz]]
  -- the separable piece: `bslOp α (α φ ψ) = α φ Γ̄ − α²(𝒜φ) ψ`
  have hsep : Work.Elliptic.bslOp α (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ') z θ
      = α * Work.FTS.VocabO.phiR z * Work.FTS.VocabO.GamBar α θ
        - α ^ 2 * Work.FTS.VocabO.phiA α z * ψ θ := by
    rw [bslOp_sep α (fun z' => α * Work.FTS.VocabO.phiR z') ψ z θ, hψeq θ hmem]
    have hd1 : deriv (fun z' => α * Work.FTS.VocabO.phiR z') z
        = α * deriv Work.FTS.VocabO.phiR z :=
      deriv_const_mul α (hphi.differentiableAt (by norm_num))
    have hd2 : iteratedDeriv 2 (fun z' => α * Work.FTS.VocabO.phiR z') z
        = α * iteratedDeriv 2 Work.FTS.VocabO.phiR z :=
      iteratedDeriv_const_mul α hphi
    have hcoef : α ^ 2 * z ^ 2 * (α * iteratedDeriv 2 Work.FTS.VocabO.phiR z)
        + α * (5 + α) * z * (α * deriv Work.FTS.VocabO.phiR z)
        = α ^ 2 * Work.FTS.VocabO.phiA α z := by
      rw [Work.FTS.VocabO.phiA]; ring
    rw [hd1, hd2, hcoef]
  rw [Work.Elliptic.bslOp_add α (fun z' θ' => Gz z' * Real.sin (2 * θ'))
        (fun z' θ' => α * Work.FTS.VocabO.phiR z' * ψ θ') z θ hcos hCd1 hCd2]
  rw [hrad, hsep]
  simp only [Work.Construction.Fstar, Work.FTS.VocabO.GamBar, Work.FTS.VocabO.phiR, Work.FM.Fstar]
  ring

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkMem_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H^k`-membership and the `H^k`-norm of a pointwise limit

This file proves `Work.FTS.StrongEps.HkMem_of_tendsto`: the `ℋ^k`-membership and the uniform
`ℋ^k`-bound of a limit `f` of a sequence `G n` of profiles of class `ℋ^m` (`m ≥ k`), from

* the pointwise convergence of *every* mixed slot `D_z^jD_θ^i` with `i + j ≤ k` on the open
  quadrant,
* a uniform `ℋ^m`-bound `HkNorm α m (G n) ≤ B`,
* a `z`-dependent uniform bound on the angular `ℋ^k`-integrals of the approximants.

The proof applies Fatou's lemma twice (the engine
`Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice`): the pointwise convergence of the slots makes
the `ℋ^k`-integrand of `f` the (pointwise) liminf of those of the approximants, and the uniform
bounds give the two uniform domination hypotheses.  The engine also needs the *measurability* of
the slice and of the angular integral of the limit integrand; both are supplied here from the
hypothesis that `f` is `C^k` on the open quadrant, via the finite-order form of the
`D_z`/`D_θ`-calculus (`continuousOn_HkIntegrand_fin`) and the two measurability lemmas
`Work.Spaces.aesm_slice_of_continuousOn_Qd` / `Work.Spaces.aesm_of_continuousOn_Qd`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real Topology

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The finite-order `D`-calculus on an open set

`Work.FTS.LocData.SmoothChain` proves that `pz`, `pth`, `Dz`, `Dth` and their iterates preserve
`C^∞` on an open set.  Here the same calculus is needed at the *finite* order `k` in which the
hypotheses of the statement are phrased, so the lemmas are repeated with a natural-number order.
-/

/-- `∂_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `∂_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-- `D_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := contDiffOn_uncurry_pz_fin hV h
  have hfun : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `D_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_uncurry_Dth_fin {G : ℝ → ℝ → ℝ} {n : ℕ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := contDiffOn_uncurry_pth_fin hV h
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
    hsin.mul hpth
  refine hfun.congr (fun p hp => ?_)
  rfl

/-- `D_z^i` lowers the differentiability order by `i` on an open set. -/
theorem contDiffOn_uncurry_DzIter_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (i n : ℕ) (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ]
      refine contDiffOn_uncurry_Dz_fin hV (ih (n + 1) ?_)
      exact h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))

/-- `D_θ^i` lowers the differentiability order by `i` on an open set. -/
theorem contDiffOn_uncurry_DthIter_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (i n : ℕ) (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      refine contDiffOn_uncurry_Dth_fin hV (ih (n + 1) ?_)
      exact h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))

/-- **The slots of `HkIntegrand α k F` are continuous on the open quadrant** as soon as `F` is
`C^k` there: `D_z^i F` for `i ≤ k` and `D_z^jD_θ^iF` for `i + j ≤ k`. -/
theorem continuousOn_DzIter_of_contDiffOn {G : ℝ → ℝ → ℝ} {k i : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hi : i ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.DzIter i G)) Work.FTS.EllipticEst.Q0 := by
  have h' : ContDiffOn ℝ ((k - i) + i : ℕ) (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
    rwa [Nat.sub_add_cancel hi]
  exact (contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 i (k - i) h').continuousOn

/-- The mixed slots `D_z^jD_θ^iF` (`i + j ≤ k`) are continuous on the open quadrant as soon as
`F` is `C^k` there. -/
theorem continuousOn_mixed_of_contDiffOn {G : ℝ → ℝ → ℝ} {k j i : ℕ}
    (h : ContDiffOn ℝ k (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hji : i + j ≤ k) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 := by
  have hi : i ≤ k := by omega
  have hj : j ≤ k - i := by omega
  have h1 : ContDiffOn ℝ (k - i) (Function.uncurry (Work.Spaces.DthIter i G))
      Work.FTS.EllipticEst.Q0 := by
    have h' : ContDiffOn ℝ ((k - i) + i : ℕ) (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
      rwa [Nat.sub_add_cancel hi]
    exact contDiffOn_uncurry_DthIter_shift Work.FTS.EllipticEst.isOpen_Q0 i (k - i) h'
  have h1' : ContDiffOn ℝ ((k - i - j) + j : ℕ) (Function.uncurry (Work.Spaces.DthIter i G))
      Work.FTS.EllipticEst.Q0 := by
    rwa [Nat.sub_add_cancel hj]
  exact (contDiffOn_uncurry_DzIter_shift Work.FTS.EllipticEst.isOpen_Q0 j (k - i - j)
    h1').continuousOn

/-! ## Continuity of the weights and of the `ℋ^k`-integrand on the open quadrant -/

/-- The angular weight `W = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0_fin (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- **The `ℋ^k`-integrand of a `C^k` datum is continuous on the open quadrant.**  Every slot
occurring in `HkIntegrand α k F` has order at most `k`, so `C^k`-regularity of `F` on the open
quadrant suffices. -/
theorem continuousOn_HkIntegrand_fin (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hz : ∀ i : ℕ, i ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_DzIter_of_contDiffOn hF hi
  have hm : ∀ j i : ℕ, i + j ≤ k → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    fun j i hji => continuousOn_mixed_of_contDiffOn hF hji
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i F p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i F p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact (((hz i hik).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact (((hm j i h.2).mul (continuousOn_Wt_Q0_fin α))).pow 2
    · exact continuousOn_const

/-! ## Measurability and integrability of the `ℋ^k`-integrand of a `C^k` datum -/

/-- At `z = 0` the radial weight `w` vanishes and with it every summand of the `ℋ^k`-integrand. -/
theorem HkIntegrand_eq_zero_at_z_zero (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k F 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

/-- The angular slices of the `ℋ^k`-integrand of a `C^k` datum are a.e. strongly measurable. -/
theorem aesm_slice_HkIntegrand_of_contDiffOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k F z θ) (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | hz0
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_HkIntegrand_fin α k F hF)
      hzpos
  · subst hz0
    rw [show (fun θ => Work.Spaces.HkIntegrand α k F 0 θ) = fun _ : ℝ => (0 : ℝ) from
      funext fun θ => HkIntegrand_eq_zero_at_z_zero α k F θ]
    exact aestronglyMeasurable_const

/-- The angular integral of the `ℋ^k`-integrand of a `C^k` datum is a.e. strongly measurable
on the half-line. -/
theorem aesm_integral_HkIntegrand_of_contDiffOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
    (continuousOn_HkIntegrand_fin α k F hF)).integral_prod_right'

/-- **`ℋ^k`-membership descends in the order**, for a datum only known to be `C^k` on the open
quadrant: the extra order-`k` regularity is used only to make the smaller integrand measurable,
which is exactly what `Integrable.mono'` needs. -/
theorem HkMem_mono_of_contDiffOn {α : ℝ} {k m : ℕ} (hkm : k ≤ m) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hm : Work.Spaces.HkMem α m F) : Work.Spaces.HkMem α k F := by
  constructor
  · intro z hz
    refine Integrable.mono' (hm.1 z hz) (aesm_slice_HkIntegrand_of_contDiffOn α k F hF z hz) ?_
    filter_upwards with θ
    rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact Work.FTS.StrongLWP.HkIntegrand_mono α F hkm z θ
  · refine Integrable.mono' hm.2 (aesm_integral_HkIntegrand_of_contDiffOn α k F hF) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k F z θ)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k F z θ) (hm.1 z hz)
      (Eventually.of_forall fun θ => Work.FTS.StrongLWP.HkIntegrand_mono α F hkm z θ)

/-! ## Pointwise convergence of the `ℋ^k`-integrand from that of the slots -/

/-- **Slot-wise convergence gives convergence of the `ℋ^k`-integrand.**  The integrand is an
explicit finite sum of squares of the slots `D_z^i` (`i ≤ k`) and `D_z^jD_θ^i` (`1 ≤ i`,
`i + j ≤ k`), so convergence of all of them gives convergence of the sum. -/
theorem HkIntegrand_tendsto_of_mixed {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    {Fs : ℕ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hconv : ∀ j i : ℕ, j + i ≤ k → Filter.Tendsto
      (fun n => Work.Spaces.mixed j i (Fs n) z θ) Filter.atTop
      (nhds (Work.Spaces.mixed j i F z θ))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (Fs n) z θ) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α k F z θ)) := by
  have hDz : ∀ i : ℕ, i ≤ k → Filter.Tendsto (fun n => Work.Spaces.DzIter i (Fs n) z θ)
      Filter.atTop (nhds (Work.Spaces.DzIter i F z θ)) :=
    fun i hi => by
      simpa only [Work.Spaces.mixed_zero_right] using hconv i 0 (by omega)
  simp only [Work.Spaces.HkIntegrand]
  refine Filter.Tendsto.add ?_ ?_
  · refine tendsto_finset_sum _ fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact ((hDz i hik).mul_const _).pow 2
  · refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hfun1 : (fun n => (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun n => (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        funext fun n => if_pos hc
      have hfun2 : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          = (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 := if_pos hc
      rw [hfun1, hfun2]
      exact ((hconv j i (by omega)).mul_const (Work.Spaces.Wt α z θ)).pow 2
    · have hfun1 : (fun n => (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (Fs n) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun _ => (0 : ℝ) := funext fun n => if_neg hc
      have hfun2 : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = (0 : ℝ) :=
        if_neg hc
      rw [hfun1, hfun2]
      exact tendsto_const_nhds

/-! ## The target -/

theorem HkMem_of_tendsto {α B : ℝ} {k m : ℕ} (hkm : k ≤ m) {G : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ (k : ℕ) (Function.uncurry (G n))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hreg : ContDiffOn ℝ (k : ℕ) (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : ∀ j i : ℕ, j + i ≤ k → ∀ z θ, (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (G n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i f z θ)))
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α m (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α m (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkNorm α k f ≤ B := by
  -- the level-`k` membership of the approximants, from their level-`m` membership
  have hmemG : ∀ n : ℕ, Work.Spaces.HkMem α k (G n) :=
    fun n => HkMem_mono_of_contDiffOn hkm (hsm n) (hmem n)
  -- the level-`k` bounds of the approximants: `HkSq α k ≤ HkSq α m = HkNorm α m ^ 2 ≤ B ^ 2`
  have hbSq : ∀ n : ℕ, Work.Spaces.HkSq α k (G n) ≤ B ^ 2 := by
    intro n
    refine le_trans (Work.FTS.StrongLWP.HkSq_mono_of_mem (k := m) (k' := k) hkm (hmem n)) ?_
    have hsq : Work.Spaces.HkSq α m (G n) = Work.Spaces.HkNorm α m (G n) ^ 2 := by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α m (G n))]
    rw [hsq]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α m (G n)) (hb n) 2
  -- the a.e. domination of the limit integrand by the `liminf` of the approximants
  have hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (G n) z θ) Filter.atTop := by
    intro z hz'
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz') with hzpos | hz0
    · have hμ : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) :=
        (Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
            (b := (π / 2)))).symm
      rw [hμ]
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hmem' : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hzpos, hθ⟩
      have hc := HkIntegrand_tendsto_of_mixed (α := α) (k := k) (F := f) (Fs := G)
        (z := z) (θ := θ) (fun j i hji => hconv j i hji z θ hmem')
      rw [hc.liminf_eq]
    · subst hz0
      filter_upwards with θ
      have hzero : (fun n : ℕ => Work.Spaces.HkIntegrand α k (G n) 0 θ) = fun _ : ℕ => (0 : ℝ) :=
        funext fun n => HkIntegrand_eq_zero_at_z_zero α k (G n) θ
      rw [HkIntegrand_eq_zero_at_z_zero α k f θ, hzero, Filter.liminf_const]
  -- Fatou, twice
  obtain ⟨hmemf, hsq⟩ := Work.FTS.EllExist.Honesty.hkMem_of_liminf_slice
    (α := α) (k := k) (f := f) (fs := G) (C := B ^ 2) (sq_nonneg B)
    hmemG hbSq
    (aesm_slice_HkIntegrand_of_contDiffOn α k f hreg)
    (aesm_integral_HkIntegrand_of_contDiffOn α k f hreg) hae hz
  refine ⟨hmemf, ?_⟩
  have hB0 : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α m (G 0)) (hb 0)
  calc Work.Spaces.HkNorm α k f = Real.sqrt (Work.Spaces.HkSq α k f) := rfl
    _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B := Real.sqrt_sq hB0

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.DthFstar_W6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-
# The `D_θ F_*`-package at order six

`Work.FTS.Nonlinear.FstarPkg.DthFstar_W` proves the level-`4` statement
`𝒲^{4,∞}(D_θ F_*) ≤ C α²`.  Here we extend it to level `6`, which needs the angular weighted
estimate `|D_θ^m Γ| ·  sin(2θ)^{-α/5}/(α + sin 2θ) ≤ K α` for `2 ≤ m ≤ 7` instead of `m ≤ 5`.
Everything else in the level-`4` proof was already level-generic (the factorisation
`pzIter k (DthIter j (Dth F_*)) = (2α/c) · hKer^{(k)} · D_θ^{j+1}Γ` holds for all `j,k`, the
radial bound `pzIter_hKer_bound` for all `k`).

The point of this file is therefore the *two extra induction steps* of the weighted angular
estimate.  They are obtained without any explicit polynomial computation: instead of the sharp
pointwise bound `|D_θ^m q| ≤ 1000 sin²(2θ)` (which was computed by hand for `m ≤ 4`), we use

* the *numerical* `qBound m` (a compactness bound for `|D_θ^m q|` on `[0,π/2]`, whose value is
  irrelevant), and
* the elementary weight inequality `sin 2θ · Γ · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1`
  (`sin_Gam_Wt_le_one`), which is exactly what makes the *top* summand `a = m` of the Leibniz
  expansion `D_θ^{m+1}Γ = α ∑_a C(m,a) (D_θ^a q)(D_θ^{m-a}Γ)` harmless: the factor
  `D_θ^m q = sin 2θ · (D_θ^{m-1}q)'` supplies the single factor of `sin 2θ` needed.

Both the `α Γ Wt ≤ 1` and the `sin 2θ Γ Wt ≤ 1` inequalities are used in the two non-top cases.
-/

namespace W6Aux

open Work.FTS.Nonlinear.FstarPkg.DthAux

/-! ## Numerical bounds for the iterates of `qfun` -/

/-- A uniform bound for `|D_θ^a q|` on `[0,π/2]`, always at least `1`. -/
noncomputable def Qb (a : ℕ) : ℝ := max (Work.Spaces.qBound a) 1

lemma Qb_pos (a : ℕ) : 0 < Qb a := lt_of_lt_of_le one_pos (le_max_right _ _)

lemma Qb_nonneg (a : ℕ) : 0 ≤ Qb a := le_of_lt (Qb_pos a)

lemma abs_iter_qfun_le_Qb (a : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| ≤ Qb a :=
  le_trans (Work.Spaces.dthU_qfun_le_qBound a hθ) (le_max_left _ _)

/-- The sum of the first `m+1` constants `Qb`. -/
noncomputable def Qs (m : ℕ) : ℝ := ∑ a ∈ Finset.range (m + 1), Qb a

lemma Qs_nonneg (m : ℕ) : 0 ≤ Qs m :=
  Finset.sum_nonneg fun a _ => Qb_nonneg a

lemma Qb_le_Qs {a m : ℕ} (ha : a ≤ m) : Qb a ≤ Qs m :=
  Finset.single_le_sum (fun i _ => Qb_nonneg i) (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

/-- `|(D_θ^m q)'|` is bounded on `[0,π/2]`. -/
lemma deriv_iter_qfun_bounded (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun) θ| ≤ B := by
  have hcd : ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.Spaces.dthU^[m] Work.Spaces.qfun) :=
    Work.Spaces.dthU_iter_smooth Work.Spaces.qfun_smooth m
  have hcont : ContinuousOn (deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun))
      (Set.Icc 0 (π / 2)) :=
    (hcd.continuous_deriv (by simp)).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
  have h := hC θ hθ
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

noncomputable def dqB (m : ℕ) : ℝ := Classical.choose (deriv_iter_qfun_bounded m)

lemma dqB_nonneg (m : ℕ) : 0 ≤ dqB m :=
  (Classical.choose_spec (deriv_iter_qfun_bounded m)).1

lemma deriv_iter_qfun_le_dqB (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |deriv (Work.Spaces.dthU^[m] Work.Spaces.qfun) θ| ≤ dqB m :=
  (Classical.choose_spec (deriv_iter_qfun_bounded m)).2 θ hθ

/-- `D_θ^j q = sin 2θ · (D_θ^{j-1}q)'` for `j ≥ 1`. -/
lemma dthU_iter_pointwise {j : ℕ} (hj : 1 ≤ j) (θ : ℝ) :
    Work.Spaces.dthU^[j] Work.Spaces.qfun θ
      = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j - 1] Work.Spaces.qfun) θ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]

/-! ## The one-factor weight inequality -/

/-- `sin 2θ · Γ · sin(2θ)^{-α/5}/(α + sin 2θ) ≤ 1`: a single factor of `sin 2θ` suffices to
absorb the weight `Wt`, because `Γ · sin(2θ)^{-α/5} ≤ 1`. -/
lemma sin_Gam_Wt_le_one {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩
  have hA : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 :=
    Work.FTS.Nonlinear.FstarPkg.GamSinRpowMulLeOne hα hα1 hθ
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  rw [Wt,
    show Real.sin (2 * θ) * Work.Spaces.Gam α θ
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (Real.sin (2 * θ) * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))))
        / (α + Real.sin (2 * θ)) from by ring,
    div_le_one hden]
  nlinarith [hs0, hA]

/-! ## The two extra Leibniz steps -/

/-- The per-summand budget of the `m ↦ m+1` step. -/
noncomputable def Bsum (m : ℕ) (K : ℝ) : ℝ :=
  Qb 0 * K + Qs m * TM m + dqB (m - 1)

lemma Bsum_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bsum m K := by
  rw [Bsum]
  have h2 : 0 ≤ Qs m * TM m := mul_nonneg (Qs_nonneg m) (le_of_lt (TM_pos m))
  have h3 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
  have h1 : 0 ≤ Qb 0 * K := mul_nonneg (Qb_nonneg 0) hK
  linarith

/-- The budget for a fixed binomial coefficient `C(m,a) ≤ 2^m`. -/
noncomputable def CQ (m : ℕ) (K : ℝ) : ℝ := (2 : ℝ) ^ m * Bsum m K

lemma CQ_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ CQ m K := by
  rw [CQ]
  exact mul_nonneg (by positivity) (Bsum_nonneg hK)

/-- The `m ↦ m+1` budget. -/
noncomputable def Bstep2 (m : ℕ) (K : ℝ) : ℝ := ((m : ℝ) + 1) * CQ m K

lemma Bstep2_nonneg {m : ℕ} {K : ℝ} (hK : 0 ≤ K) : 0 ≤ Bstep2 m K := by
  rw [Bstep2]
  have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  exact mul_nonneg this (CQ_nonneg hK)

/-- The bound for a single summand of the Leibniz expansion at order `m ≥ 2`. -/
lemma summand_le2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {a : ℕ} (ha : a ≤ m) :
    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
        Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
      ≤ Bsum m K := by
  have hW : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- `a = 0`: the induction hypothesis, times `|q| ≤ Qb 0`
    subst ha0
    simp only [Function.iterate_zero_apply, Nat.sub_zero]
    have hIH := hKm α hα hα1 θ hθ
    have hq := abs_iter_qfun_le_Qb 0 hθ
    have hstep : |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ) ≤ Qb 0 * (K * α) :=
      mul_le_mul hq hIH (mul_nonneg (abs_nonneg _) hW) (Qb_nonneg 0)
    have hfin : Qb 0 * (K * α) ≤ Qb 0 * K := by
      apply mul_le_mul_of_nonneg_left _ (Qb_nonneg 0)
      nlinarith [hK0, hα, hα1]
    have h1 : Qb 0 * K ≤ Bsum m K := by
      rw [Bsum]
      have hTM := TM_pos m
      have hd := dqB_nonneg (m - 1)
      have hQ := Qs_nonneg m
      nlinarith [mul_nonneg hQ (le_of_lt hTM)]
    calc |Work.Spaces.qfun θ * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
        = |Work.Spaces.qfun θ| * (|Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
            * Wt α θ) := by rw [abs_mul]; ring
      _ ≤ Qb 0 * (K * α) := hstep
      _ ≤ Qb 0 * K := hfin
      _ ≤ Bsum m K := h1
  · rcases eq_or_lt_of_le ha with ham | ham
    · -- `a = m`: `D_θ^m q = sin 2θ · (D_θ^{m-1}q)'` supplies the factor of `sin 2θ`
      rw [ham]
      have hs0 : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
          by linarith [hθ.2, Real.pi_pos]⟩
      have hpt := dthU_iter_pointwise (j := m) (by omega) θ
      have hk : |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * Wt α θ
          ≤ dqB (m - 1) := by
        rw [hpt, abs_mul, abs_of_nonneg hs0]
        have hsin := sin_Gam_Wt_le_one hα hα1 hθ
        have hle : |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
            ≤ dqB (m - 1) := deriv_iter_qfun_le_dqB (m - 1) hθ
        have hd0 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
        calc Real.sin (2 * θ) * |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
              * Work.Spaces.Gam α θ * Wt α θ
            = |deriv (Work.Spaces.dthU^[m - 1] Work.Spaces.qfun) θ|
              * (Real.sin (2 * θ) * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ dqB (m - 1) * 1 :=
              mul_le_mul hle hsin (mul_nonneg (mul_nonneg hs0 hG0) hW) hd0
          _ = dqB (m - 1) := by ring
      have h1 : dqB (m - 1) ≤ Bsum m K := by
        rw [Bsum]
        have hTM := TM_pos m
        have hQ := Qs_nonneg m
        have h1 : 0 ≤ Qb 0 * K := mul_nonneg (Qb_nonneg 0) hK0
        have h2 : 0 ≤ Qs m * TM m := mul_nonneg hQ (le_of_lt hTM)
        have h3 : 0 ≤ dqB (m - 1) := dqB_nonneg (m - 1)
        linarith
      calc |Work.Spaces.dthU^[m] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          = |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| * Work.Spaces.Gam α θ * Wt α θ := by
            simp only [Nat.sub_self, Function.iterate_zero_apply, abs_mul,
              abs_of_nonneg hG0]
        _ ≤ dqB (m - 1) := hk
        _ ≤ Bsum m K := h1
    · -- `1 ≤ a ≤ m-1`: the crude bound for `D_θ^{m-a}Γ`
      have ha1 : 1 ≤ a := hapos
      have hm1 : 1 ≤ m - a := by omega
      have hQ := abs_iter_qfun_le_Qb a hθ
      have hQ' : Qb a ≤ Qs m := Qb_le_Qs ha
      have hCrude := Work.Spaces.dthU_Gam_le (m - a) hm1 α hα hα1 θ hθ
      have htB : Work.Spaces.tBound (m - a - 1) 0 ≤ TM m := tBound_le_TM (by omega)
      have hk : |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ Qs m * TM m := by
        rw [abs_mul]
        have h2 : |Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|
            ≤ α * TM m * Work.Spaces.Gam α θ :=
          le_trans hCrude (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htB hα.le) hG0)
        have h1 : α * Work.Spaces.Gam α θ * Wt α θ ≤ 1 := by
          have h := alpha_Gam_Wt_le_one hα hθ
          linarith [h]
        calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ| *
              |Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
            ≤ Qs m * (α * TM m * Work.Spaces.Gam α θ) * Wt α θ := by
              apply mul_le_mul_of_nonneg_right _ hW
              exact mul_le_mul (le_trans hQ hQ') h2 (abs_nonneg _) (Qs_nonneg m)
          _ = Qs m * TM m * (α * Work.Spaces.Gam α θ * Wt α θ) := by ring
          _ ≤ Qs m * TM m * 1 := by
              apply mul_le_mul_of_nonneg_left h1
              exact mul_nonneg (Qs_nonneg m) (le_of_lt (TM_pos m))
          _ = Qs m * TM m := by ring
      have h1 : Qs m * TM m ≤ Bsum m K := by
        rw [Bsum]
        have hd := dqB_nonneg (m - 1)
        have h0 := mul_nonneg (Qb_nonneg 0) hK0
        linarith
      calc |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
            Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ
          ≤ Qs m * TM m := hk
        _ ≤ Bsum m K := h1

/-- **The Leibniz step at order `m ≥ 2`**: the weighted bound at order `m+1` from the bound at
order `m`, valid for every `m ≥ 2` (no upper bound on `m` is needed). -/
lemma step2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K)
    (hKm : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m + 1] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ Bstep2 m K * α := by
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  by_cases hI : θ ∈ Set.Ioo 0 (π / 2)
  · have hGam_diff : ContDiffOn ℝ ⊤ (fun t => Work.Spaces.Gam α t) (Set.Ioo 0 (π / 2)) :=
      contDiffOn_Gam_Ioo' α
    have hq_diff : ContDiffOn ℝ ⊤ Work.Spaces.qfun (Set.Ioo 0 (π / 2)) := by
      show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - 1 / 3) (Set.Ioo 0 (π / 2))
      fun_prop
    have hEqOn : Set.EqOn (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) (Set.Ioo 0 (π / 2)) := by
      intro t ht
      rw [Work.Spaces.dthU_Gam α t hα ht]
      ring
    have hmain : Work.Spaces.dthU^[m + 1] (fun t => Work.Spaces.Gam α t) θ
        = α * (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)) := by
      rw [Function.iterate_succ_apply]
      rw [dthU_iter_congr_open isOpen_Ioo m (Work.Spaces.dthU (fun t => Work.Spaces.Gam α t))
        (fun t => α * (Work.Spaces.qfun t * Work.Spaces.Gam α t)) hEqOn hI]
      simp only [Work.Spaces.dthU_iter_const_mul]
      rw [show (fun θ : ℝ => Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
          = (Work.Spaces.qfun * fun θ : ℝ => Work.Spaces.Gam α θ) from rfl]
      rw [dthU_iter_mul_Ioo m Work.Spaces.qfun (fun θ : ℝ => Work.Spaces.Gam α θ) hI
        hq_diff hGam_diff]
    have hsum : |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        ≤ ((m : ℝ) + 1) * CQ m K := by
      have habs : |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
            (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
              Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)|
          ≤ ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| := by
        calc |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)|
            ≤ ∑ a ∈ Finset.range (m + 1), |(m.choose a : ℝ) *
                (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.choose a))]
      have h2 : (∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
          ≤ ((m : ℝ) + 1) * CQ m K := by
        rw [Finset.sum_mul]
        calc ∑ a ∈ Finset.range (m + 1), ((m.choose a : ℝ) *
                |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                  Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
            ≤ ∑ _a ∈ Finset.range (m + 1), CQ m K := by
              apply Finset.sum_le_sum
              intro a ha
              have ham : a ≤ m := by
                have := Finset.mem_range.mp ha
                omega
              have hX := summand_le2 m hm hK0 hKm hα hα1 hθ ham
              have hb : (m.choose a : ℝ) ≤ (2 : ℝ) ^ m := by
                exact_mod_cast Nat.choose_le_two_pow m a
              have hX0 : 0 ≤ |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                    Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ :=
                mul_nonneg (abs_nonneg _) hW0
              calc ((m.choose a : ℝ) *
                    |Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                      Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ|) * Wt α θ
                  = (m.choose a : ℝ) *
                      (|Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                        Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ) := by
                    ring
                _ ≤ (2 : ℝ) ^ m * Bsum m K :=
                    mul_le_mul hb hX hX0 (by positivity)
                _ = CQ m K := by rw [CQ]
          _ = ((m : ℝ) + 1) * CQ m K := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              push_cast
              ring
      exact le_trans (mul_le_mul_of_nonneg_right habs hW0) h2
    rw [hmain, abs_mul, abs_of_pos hα]
    calc α * |∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ
        = α * (|∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) *
              (Work.Spaces.dthU^[a] Work.Spaces.qfun θ *
                Work.Spaces.dthU^[m - a] (fun t => Work.Spaces.Gam α t) θ)| * Wt α θ) := by ring
      _ ≤ α * (((m : ℝ) + 1) * CQ m K) := mul_le_mul_of_nonneg_left hsum hα.le
      _ = Bstep2 m K * α := by rw [Bstep2]; ring
  · -- angular endpoints: the weight vanishes
    have hs : Real.sin (2 * θ) = 0 := by
      rcases lt_or_eq_of_le hθ.1 with h0 | h0
      · have h1 : θ = π / 2 := le_antisymm hθ.2 (le_of_not_gt (fun h => hI ⟨h0, h⟩))
        rw [h1, show 2 * (π / 2) = π by ring, Real.sin_pi]
      · rw [← h0]; simp
    have hWz : Wt α θ = 0 := by
      rw [Wt, hs, Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
      simp
    rw [hWz, mul_zero]
    exact mul_nonneg (Bstep2_nonneg hK0) hα.le

/-- One step of the induction, valid for any `m ≥ 2`. -/
lemma Good_step2 (m : ℕ) (hm : 2 ≤ m) {K : ℝ} (hK0 : 0 ≤ K) (hK : Good m K) :
    Good (m + 1) (max K (Bstep2 m K)) := by
  intro m' hm2 hm' α hα hα1 θ hθ
  by_cases hle : m' ≤ m
  · have h1 := hK m' hm2 hle α hα hα1 θ hθ
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le)
  · have hm'eq : m' = m + 1 := by omega
    rw [hm'eq]
    have h2 := step2 m hm hK0 (hK m hm (le_refl m)) α hα hα1 θ hθ
    exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le)

/-- The weighted angular estimate at orders `2 ≤ m ≤ 6`. -/
lemma Good_six : Good 6 (max K5 (Bstep2 5 K5)) :=
  Good_step2 5 (by norm_num) (le_of_lt K5_pos) Good_five

/-- The weighted angular estimate at orders `2 ≤ m ≤ 7`. -/
lemma Good_seven : Good 7 (max (max K5 (Bstep2 5 K5))
    (Bstep2 6 (max K5 (Bstep2 5 K5)))) :=
  Good_step2 6 (by norm_num)
    (le_trans (le_of_lt K5_pos) (le_max_left _ _)) Good_six

/-- **The weighted angular estimate at orders `2 ≤ m ≤ 7`.** -/
theorem dthGamWeightLe7 : ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → m ≤ 7 →
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| * Wt α θ ≤ K * α := by
  refine ⟨max (max K5 (Bstep2 5 K5)) (Bstep2 6 (max K5 (Bstep2 5 K5))),
    lt_of_lt_of_le K5_pos (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro m hm hm7
  exact Good_seven m hm hm7

/-! ## The level-`l` assembly

The remainder of the level-`4` proof (`DthFstar_mixed_bound`, `KD`, `WlInfMem_DthFstar`,
`WlInf_DthFstar_le`) is level-independent except for the explicit numerals `4`, `5`: the
factorization `FstarDthFactor` holds for all `j,k`, the radial bound `pzIter_hKer_bound` for all
`k`, and the angular input is used only through the hypothesis `hK` on the orders `2 ≤ m ≤ l+1`.
We therefore prove the level-`l` statements once and specialise to `l = 6`. -/

/-- The universal constant of the level-`l` estimate for `D_θF_*`. -/
noncomputable def KBl (l : ℕ) (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), 20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)))
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        (if 1 ≤ j ∧ k + j ≤ l then 20 * K * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KBl_nonneg (l : ℕ) {K : ℝ} (hK : 0 ≤ K) : 0 ≤ KBl l K := by
  rw [KBl]
  refine add_nonneg (Finset.sum_nonneg fun k _ => ?_)
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  · exact mul_nonneg (mul_nonneg (by norm_num) (Work.Spaces.tBound_nonneg _ _)) (by positivity)
  · split_ifs with h
    · exact mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)
    · norm_num

/-- The mixed slots of `𝒲^{l,∞}(D_θF_*)`. -/
lemma DthFstar_mixed_bound_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j k : ℕ) (hj : 1 ≤ j) (hjl : j ≤ l)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z+1)^k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
  rw [show (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ
        * (Real.sin (2*θ)) ^ (-(α/5)) / (α + Real.sin (2*θ))
      = (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (Work.Spaces.Dth (Work.Construction.Fstar α))) z θ * Wt α θ from by
    rw [Wt]; ring]
  rw [FstarDthFactor α j k z θ]
  have hker : |(z + 1) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) :=
    Work.Spaces.pzIter_hKer_bound k z hz
  have hcoef := Fstar_coef_leD' α hα hα1
  have hW0 : 0 ≤ Wt α θ := Wt_nonneg hα hθ
  have hdth := hK (j+1) (by omega) (by omega) α hα hα1 θ hθ
  have hloc : (z + 1) ^ k * ((2 * α / Work.Spaces.c α) * deriv^[k] Work.Spaces.hKer z
        * Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ) * Wt α θ
      = (2 * α / Work.Spaces.c α) * ((z + 1) ^ k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ) := by ring
  have hmain : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)
        * (Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ)|
      ≤ (20 * K * ((k.factorial : ℝ) * (k+1))) * α^2 := by
    rw [abs_mul]
    have hAB : |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
        ≤ 20 * α * ((k.factorial : ℝ) * (k + 1)) := by
      rw [abs_mul]
      exact mul_le_mul hcoef hker (abs_nonneg _) (by positivity)
    have hdW : |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ| ≤ K * α := by
      rw [abs_mul, abs_of_nonneg hW0]
      exact hdth
    calc |(2 * α / Work.Spaces.c α) * ((z+1)^k * deriv^[k] Work.Spaces.hKer z)|
          * |Work.Spaces.dthU^[j+1] (fun t => Work.Spaces.Gam α t) θ * Wt α θ|
        ≤ (20 * α * ((k.factorial : ℝ) * (k + 1))) * (K * α) :=
          mul_le_mul hAB hdW (abs_nonneg _) (by positivity)
      _ = (20 * K * ((k.factorial : ℝ) * (k + 1))) * α^2 := by ring
  rw [hloc]
  exact hmain

/-- Membership of `D_θF_*` in `𝒲^{l,∞}`. -/
lemma WlInfMem_DthFstar_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α l (Work.Spaces.Dth (Work.Construction.Fstar α)) := by
  constructor
  · intro k hk
    refine ⟨20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2,
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2, fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact DthFstar_mixed_bound_l hK α hα hα1 j k hj1 hj z θ hz hθ

/-- The `𝒲^{l,∞}`-norm bound for `D_θF_*`. -/
lemma WlInf_DthFstar_le_l {K : ℝ} {l : ℕ}
    (hK : ∀ m : ℕ, 2 ≤ m → m ≤ l + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        * Wt α θ ≤ K * α)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α l (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ KBl l K * α^2 := by
  have h2 : KBl l K * α^2 =
      (∑ k ∈ Finset.range (l + 1),
          20 * Work.Spaces.tBound 0 0 * ((k.factorial : ℝ) * (k + 1)) * α^2)
        + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
            (if 1 ≤ j ∧ k + j ≤ l then
              20 * K * ((k.factorial : ℝ) * (k + 1)) * α^2 else 0) := by
    rw [KBl, add_mul]
    congr 1
    · rw [Finset.sum_mul]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with h <;> ring
  rw [Work.Spaces.WlInf, h2]
  apply add_le_add
  · exact Finset.sum_le_sum fun k hk =>
      Work.Spaces.supAbs_le fun z hz θ hθ => DthFstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · exact Work.Spaces.supAbs_le fun z hz θ hθ =>
        DthFstar_mixed_bound_l hK α hα hα1 j k hcond.1 (by omega) z θ hz hθ
    · simp

end W6Aux

theorem DthFstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := W6Aux.dthGamWeightLe7
  have hK6 : ∀ m : ℕ, 2 ≤ m → m ≤ 6 + 1 → ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
          * Work.FTS.Nonlinear.FstarPkg.DthAux.Wt α θ ≤ K * α :=
    fun m hm hm7 => hK m hm hm7
  refine ⟨W6Aux.KBl 6 K + 1, by linarith [W6Aux.KBl_nonneg 6 (le_of_lt hKpos)],
    fun α hα hα1 => ⟨?_, ?_⟩⟩
  · exact W6Aux.WlInfMem_DthFstar_l hK6 α hα hα1
  · refine le_trans (W6Aux.WlInf_DthFstar_le_l hK6 α hα hα1) ?_
    have h0 : 0 ≤ α ^ 2 := sq_nonneg α
    nlinarith [W6Aux.KBl_nonneg 6 (le_of_lt hKpos), h0]

end Work.FTS.StrongPersist
end
end
