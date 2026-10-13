/-
# `Work.ConstructionInstance.Tie` — the residual `tie`, decomposed into chapter-owned statements

The repaired interface `Patch.ConstructionDataFixed α` has (after finding (H) of `NOTES.md`) four
fields: the LWP chapter's analytic input bundle `lwp`, the *inhabited* profile/modulation data
`prof : ProfileData α`, and the two named residuals

* `tie : SelfSimilarEulerSolution α prof.T prof` — the chapter's maximal solution is the
  self-similar one;
* `hThDt : SelfSimTimeHolderDeriv α prof` — the time-Hölder regularity of `∂ₜω` on strips.

This file performs the **decomposition of `tie`** promised by `NOTES.md` §3.3: it proves

> `tie`  ⟸  `lwp` + `SelfSimVorticityEquation` + `SelfSimLGClass` + `SelfSimVortSmooth`
>          + `SelfSimMaximal`,

i.e. the statement "the LWP maximal solution of the cut-off datum *is* the self-similar one" is a
*theorem* once one supplies the four analytic inputs

| residual | mathematical content | owner |
|---|---|---|
| `SelfSimVorticityEquation α P` | the ℝ³ vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u` for `u = BS ω`, `ω = solVort P` | `Work.Stability` (`DynEq`/`SelfSimEulerS`/`GEquationWithFar`, through the `Cyl` dictionary) |
| `SelfSimLGClass α P` | the *spacetime* Lichtenstein–Gunther class of `BS(ω(·,t))` on the strips `[0,S]`, `S < T` (this is `Work.LWP.SpaceTimeHolder`, the LWP chapter's own notion) | `Work.LWP` (the Picard iteration; the per-slice Schauder input `BiotSavartSchauder` is *not* enough) |
| `SelfSimVortSmooth α P` | `C¹` of the ansatz velocity on the *two-sided* open window `(-2,T)` (the construction's backward extension) | `Work.Construction`/`Work.LWP` |
| `SelfSimMaximal α P` | `T` is the maximal time of existence, i.e. the ansatz admits no extension past `T` | `Work.StabilityFar` (`St5` + Beale–Kato–Majda; `bkm_divergence_of_st5` below is the quantitative half) |

The reduction itself uses only the *delivered* LWP machinery: the pressure reconstruction
(`LWPInputs.pressure`) turns the vorticity equation plus the spacetime class into an Euler solution
with the cut-off datum `BS ω₀` (the datum matching is the normalisation `λ̄(0) = 1`,
`Reduced.solVort_zero_eq_cutDatum`), and the oddness of the velocity is
`isOdd_biotSavart_solVort`.  In particular the four residuals are *independent* of each other and
of the interface, and each is stated in the vocabulary of the chapter that owns it.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.Patch
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.isOdd_biotSavart_solVort
import Submission.Work.ConstructionInstance.vorticity_biotSavart_solVort
import Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le
import Submission.Work.LWP.Main

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

theorem ansatzV_apply {α : NNReal} (P : ProfileData α) (x : R3) (t : ℝ) :
    ansatzV P x t = Work.LWP.biotSavart (fun y => solVort P y t) x := rfl

theorem ansatzV_uncurry {α : NNReal} (P : ProfileData α) :
    (ansatzV P).uncurry
      = fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => solVort P y q.2) q.1 := rfl

theorem ansatzV_slice {α : NNReal} (P : ProfileData α) (t : ℝ) :
    (ansatzV P · t) = fun x : R3 => Work.LWP.biotSavart (fun y => solVort P y t) x := rfl

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

/-- **The exact object behind residual 5, in `ProfileData` terms.**  Residual 5 follows from a
strip-uniform bound on the *second* time derivative of the vorticity together with the
differentiability of `t ↦ ∂ₜω(z,t)`.  (Both are true for the explicit self-similar field — the
ansatz is `C^∞` in `t` on every strip — but they need the second `z`-derivative of the profile and
the second derivative of `λ̄`, neither of which is a field of `ProfileData`; see `NOTES.md`
§3.5.) -/
theorem selfSimTimeHolderDeriv_of_secondDerivBound {α : NNReal} (P : ProfileData α) {Λ : ℝ → ℝ}
    (hΛ : ∀ S : ℝ, 0 < S → S + 1 < P.T → 0 ≤ Λ S)
    (hdiff : ∀ S : ℝ, 0 < S → S + 1 < P.T →
      ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
        HasDerivAt (fun t => FiniteTimeSingularity.timeDeriv (solVort P) z t)
          (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv (solVort P)) z s) s)
    (hbd : ∀ S : ℝ, 0 < S → S + 1 < P.T →
      ∀ z ∈ Metric.closedBall (0 : R3) P.R, ∀ s ∈ Work.StabilityFar.window S,
        ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv (solVort P)) z s‖
          ≤ Λ S) :
    SelfSimTimeHolderDeriv P := by
  intro S hS hST
  have hα1 : (α : ℝ) ≤ 1 := by linarith [P.hα13]
  exact timeHolderOnBall_timeDeriv_of_secondDeriv (α := (α : ℝ)) (Λ := Λ S)
    P.hα hα1 (hΛ S hS hST) (hdiff S hS hST) (hbd S hS hST)

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
