import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs
import Submission.Lib.Unif2.Work.Modulus.PeriodSetup
import Submission.Lib.Unif2.Work.SimplyConnected.ModulusDefs
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.conjBridgeMap
import Submission.Lib.Unif2.Work.Modulus.BranchCovering.isCoveringMap_branchProj

/-!
# The periods of the conjugate of the Green function are multiples of `2π`

Let `X` be a Riemann surface, `z₀ : X`, and `E : X → ℝ` a Green function with pole `z₀`
(`Work.UnitGreen.IsUnitGreenFunctionAt`).  The conjugate of `E` is only defined modulo the periods of the
harmonic conjugate, and the holomorphic modulus `exp (-(E + iE*))` is single-valued exactly when all
the periods are multiples of `2π` (`Work.Modulus.greenPeriodHom`).

This module computes those periods for the loops that are *null-homotopic in `X`*:  they are
multiples of `2π`.  The proof is the transport of the branches of the modulus along the homotopy:

* the bundle `Work.SC.branchProj` of local branches of the modulus is a covering space of `X`
  (`Work.Modulus.BranchCovering.isCoveringMap_branchProj`), so the transport of a branch along a
  path of `X` depends only on the homotopy class of that path;
* the conjugate étale space of `E` over the punctured surface maps to that bundle
  (`Work.Modulus.BranchCovering.conjBridgeMap`): the point of the étale space with coordinate `t`
  goes to the branch whose value is `exp (-(E x + it))`;
* hence, for a loop `γ` of `X ∖ {z₀}` which is null-homotopic in `X`, the branch is transported
  back to itself, i.e. `exp (-i·period γ) = 1`, which is the claim.

The two covering-theoretic inputs are isolated as explicit hypotheses of
`Work.Modulus.greenPeriodHom_two_pi_zmultiples_of_inputs` below; the target theorem
`Work.Modulus.greenPeriodHom_two_pi_zmultiples` discharges them from the parallel development.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

set_option linter.style.haveILetI false

noncomputable section

open Filter Set
open Classical

namespace Work.Modulus

section Aux

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The main computation, with its two covering-theoretic inputs isolated.**

* `hcovX` : the bundle of local branches of the modulus is a covering space of `X`;
* `hbridge` : the conjugate étale space of `E` over `X ∖ {z₀}` maps continuously to that bundle,
  the point of coordinate `t` going to the branch of value `exp (-(E x + it))`.

The conclusion is that the period of a loop of `X ∖ {z₀}` which is null-homotopic in `X` is a
multiple of `2π`. -/
theorem greenPeriodHom_two_pi_zmultiples_of_inputs
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀)
    (hγ : FundamentalGroup.map (ContinuousMap.mk (Subtype.val : puncturedOpens z₀ → X)
      continuous_subtype_val) u₀ γ = 1)
    (hcovX : @IsCoveringMap (Work.SC.ModulusBundle z₀ E) X (Work.SC.modulusBundleTopology z₀ E) _
      (Work.SC.branchProj z₀ E))
    (hbridge : ∃ φ : ((puncturedOpens z₀) × ℝ) → Work.SC.ModulusBundle z₀ E,
      @Continuous ((puncturedOpens z₀) × ℝ) (Work.SC.ModulusBundle z₀ E)
          (greenConjTopology z₀ E) (Work.SC.modulusBundleTopology z₀ E) φ ∧
        (∀ p : (puncturedOpens z₀) × ℝ, Work.SC.branchProj z₀ E (φ p) = p.1.1) ∧
        (∀ (x : puncturedOpens z₀) (t : ℝ),
          (φ (x, t)).1.2.1 = Complex.exp (-((E x.1 : ℂ) + (t : ℂ) * Complex.I)))) :
    ∃ k : ℤ, greenPeriodHom hE u₀ (Additive.ofMul γ) = k * (2 * Real.pi) := by
  classical
  letI : TopologicalSpace ((puncturedOpens z₀) × ℝ) := greenConjTopology z₀ E
  letI : TopologicalSpace (Work.SC.ModulusBundle z₀ E) := Work.SC.modulusBundleTopology z₀ E
  -- the conjugate étale space of `E` over the punctured surface is a covering space
  have hcovU : IsCoveringMap (Prod.fst : (puncturedOpens z₀) × ℝ → puncturedOpens z₀) :=
    green_isCoveringMap hE
  -- the bridge to the bundle of branches
  obtain ⟨φ, hφcont, hφproj, hφval⟩ := hbridge
  -- a representative of the loop
  obtain ⟨γp⟩ := γ
  -- the lift of the loop in the conjugate étale space
  let e₀ : (puncturedOpens z₀) × ℝ := (u₀, 0)
  let Γ : C(unitInterval, (puncturedOpens z₀) × ℝ) :=
    hcovU.liftPath γp e₀ (γp.source.trans (rfl : Prod.fst e₀ = u₀).symm)
  have hΓlifts : Prod.fst ∘ (Γ : unitInterval → (puncturedOpens z₀) × ℝ) =
      (γp : unitInterval → ↥(puncturedOpens z₀)) := hcovU.liftPath_lifts _ _ _
  have hΓ0 : Γ 0 = e₀ := hcovU.liftPath_zero _ _ _
  -- the period is the second coordinate of the endpoint of the lift
  have hper : greenPeriodHom hE u₀ (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) = (Γ 1).2 := by
    rw [greenPeriodHom_apply]
    have h1 : (hcovU.monodromy (Path.Homotopic.Quotient.mk γp) (Submission.conjFiberPt u₀ 0)).1 =
        Γ 1 := rfl
    have h2 : (Submission.conjFiberPt u₀ 0).1.2 = 0 := rfl
    have h3 : (hcovU.monodromy (Path.Homotopic.Quotient.mk γp) (Submission.conjFiberPt u₀ 0)).1.2 =
        (Γ 1).2 := congrArg Prod.snd h1
    simp only [Submission.conjPeriod, h3, h2, sub_zero]
  -- the image of the loop in `X`
  set incl : C(puncturedOpens z₀, X) := ⟨Subtype.val, continuous_subtype_val⟩ with hincl
  set γX : Path u₀.1 u₀.1 :=
    γp.map (f := (Subtype.val : puncturedOpens z₀ → X)) continuous_subtype_val with hγX
  have hmap : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp) =
      Path.Homotopic.Quotient.mk γX := by
    rw [show (FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp))
        = (Path.Homotopic.Quotient.mk γp).map incl from rfl]
    exact (Path.Homotopic.Quotient.mk_map γp incl).symm
  have hγ' : FundamentalGroup.map incl u₀ (Path.Homotopic.Quotient.mk γp) = 1 := hγ
  have hγX1 : Path.Homotopic.Quotient.mk γX = Path.Homotopic.Quotient.mk (Path.refl u₀.1) := by
    rw [← hmap, hγ']
    exact FundamentalGroup.one_def
  -- the homotopy of the loop to the constant loop
  have hhom : (γX : C(unitInterval, X)).HomotopicRel (ContinuousMap.const unitInterval u₀.1) {0,1} := by
    have h3 : γX.Homotopic (Path.refl u₀.1) := Path.Homotopic.Quotient.eq.mp hγX1
    exact ⟨h3.some⟩
  -- the image of the lift under the bridge
  set ΓX : C(unitInterval, Work.SC.ModulusBundle z₀ E) :=
    ⟨fun s => φ (Γ s), hφcont.comp Γ.continuous⟩ with hΓX
  have hΓXlifts : Work.SC.branchProj z₀ E ∘ (ΓX : unitInterval → Work.SC.ModulusBundle z₀ E) =
      (γX : unitInterval → X) := by
    funext s
    have hs : (Γ s).1 = γp s := congrFun hΓlifts s
    show Work.SC.branchProj z₀ E (φ (Γ s)) = γX s
    rw [hφproj, hs]
    rfl
  have hΓX0 : (ΓX : unitInterval → Work.SC.ModulusBundle z₀ E) 0 = φ e₀ := by
    show φ (Γ 0) = φ e₀
    rw [hΓ0]
  -- uniqueness of lifts in the covering space of branches
  have huniq : ΓX = hcovX.liftPath γX (φ e₀)
      ((γX.source).trans (hφproj e₀).symm) :=
    (hcovX.eq_liftPath_iff' (γ := γX) (e := φ e₀)
      (γ_0 := (γX.source).trans (hφproj e₀).symm)).mpr ⟨hΓXlifts, hΓX0⟩
  -- hence the branch is transported back to itself
  have hfinal : φ (Γ 1) = φ e₀ := by
    have h1 : φ (Γ 1) = (hcovX.liftPath γX (φ e₀)
        ((γX.source).trans (hφproj e₀).symm)) 1 := by
      rw [← huniq]
      rfl
    rw [h1]
    have h2 := hcovX.liftPath_apply_one_eq_of_homotopicRel hhom (φ e₀)
      ((γX.source).trans (hφproj e₀).symm) (hφproj e₀).symm
    rw [h2, hcovX.liftPath_const (x := u₀.1) (hpe := (hφproj e₀).symm)]
    rfl
  -- read off the values of the two branches
  have hbase1 : (Γ 1).1 = u₀ := by
    have := congrFun hΓlifts 1
    simpa using this
  have hval1 : (φ (Γ 1)).1.2.1 =
      Complex.exp (-((E u₀.1 : ℂ) + ((Γ 1).2 : ℂ) * Complex.I)) := by
    have hsplit : Γ 1 = (u₀, (Γ 1).2) := Prod.ext hbase1 rfl
    rw [hsplit]
    exact hφval u₀ (Γ 1).2
  have hval0 : (φ e₀).1.2.1 = Complex.exp (-((E u₀.1 : ℂ) + (0 : ℂ) * Complex.I)) := by
    show (φ (u₀, 0)).1.2.1 = _
    exact hφval u₀ 0
  have heqexp : Complex.exp (-((E u₀.1 : ℂ) + ((Γ 1).2 : ℂ) * Complex.I)) =
      Complex.exp (-((E u₀.1 : ℂ) + (0 : ℂ) * Complex.I)) := by
    rw [← hval1, ← hval0, hfinal]
  -- a numerator-free form of the equality of exponentials
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heqexp
  have him : -(((Γ 1).2 : ℝ)) = (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  refine ⟨-n, ?_⟩
  show greenPeriodHom hE u₀ (Additive.ofMul (Path.Homotopic.Quotient.mk γp)) = ↑(-n) * (2 * Real.pi)
  rw [hper]
  push_cast
  linarith

end Aux

/-- **The target theorem**: the periods of the conjugate of the Green function around loops which
are null-homotopic in `X` are multiples of `2π`.  This is
`Work.Modulus.greenPeriodHom_two_pi_zmultiples_of_inputs` with its two covering-theoretic inputs
supplied by the branch-bundle covering theorem and the bridge map of the conjugate étale space. -/
theorem greenPeriodHom_two_pi_zmultiples
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} (hE : Work.UnitGreen.IsUnitGreenFunctionAt z₀ E)
    (u₀ : puncturedOpens z₀) (γ : FundamentalGroup (puncturedOpens z₀) u₀)
    (hγ : FundamentalGroup.map (ContinuousMap.mk (Subtype.val : puncturedOpens z₀ → X)
      continuous_subtype_val) u₀ γ = 1) :
    ∃ k : ℤ, greenPeriodHom hE u₀ (Additive.ofMul γ) = k * (2 * Real.pi) :=
  greenPeriodHom_two_pi_zmultiples_of_inputs hE u₀ γ hγ
    (Work.Modulus.BranchCovering.isCoveringMap_branchProj hE)
    (Work.Modulus.BranchCovering.conjBridgeMap hE)

end Work.Modulus
