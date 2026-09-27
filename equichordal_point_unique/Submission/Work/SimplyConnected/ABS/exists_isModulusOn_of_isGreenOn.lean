import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.SimplyConnected.ModulusDefs
import Submission.Work.SimplyConnected.ModulusMain
import Submission.Work.Modulus.puncturedHarmonic
import Submission.Work.Modulus.isCoveringMap_branchProj_of_localBranches
import Submission.Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp
import Submission.Work.SimplyConnected.ABS.exists_localBranch_chartBall_of_isGreenOn

/-!
# The holomorphic modulus of a Green function on a simply connected domain

Hubbard, *Teichmüller theory* Vol. 1, Chapter 1; Anghel–Bruin–Stan, *Uniformization of Riemann
surfaces revisited* (arXiv:2008.12189), the disc lemma (item 10).

This module proves `Work.SimplyConnected.ABS.exists_isModulusOn_of_isGreenOn`: on an open *simply
connected* domain `Ω` of a Riemann surface `X`, a Green function `E` with pole `x₀` (in the
satisfiable form of `Work.SimplyConnected.ABS.IsGreenOn`) has a holomorphic *modulus* `Φ` on `Ω`:
`Φ` is holomorphic on `Ω`, has a simple zero at `x₀` in the preferred chart at `x₀`, and
`‖Φ x‖ = exp (-(E x))` for `x ∈ Ω`, `x ≠ x₀`.

The statement is `Work.SimplyConnected.ABS.exists_modulusOn` with the hypothesis `IsConnected Ω`
*removed*; no information is lost, because `IsSimplyConnected Ω` already implies that `Ω` is
(path)connected: `IsSimplyConnected Ω` is `SimplyConnectedSpace ↥Ω`, which is (an equivalence of the
fundamental groupoid with the terminal groupoid, hence) `PathConnectedSpace ↥Ω` and non-empty, and
`ConnectedSpace ↥Ω` is exactly `IsConnected Ω`.

## Strategy

Everything happens on the open subspace `U := ⟨Ω, hΩo⟩` of `X`, which is a Riemann surface in its own
right (open subsets inherit the charted-space and manifold structures).  On `U`:

* `E` restricted to `U` is harmonic off its pole and has a bounded logarithmic pole there, so every
  point of `U` has a chart ball carrying a *local branch* of the modulus `exp (-E)`
  (`Work.SimplyConnected.ABS.exists_localBranch_chartBall_of_isGreenOn`, a hypotheses-only restatement
  of `Work.Modulus.localHolomorphicModulus` + `Work.SimplyConnected.Modulus.exists_localBranch_of_harmonicOnXAt`);
* the bundle of local branches of the multivalued modulus `exp (-(E + iE*))` over `U`
  (`Work.SC.ModulusBundle`, whose points are the branches, encoded over the pole by the derivative) is
  therefore a covering space of `U` (`Work.Modulus.isCoveringMap_branchProj_of_localBranches`);
* `U` is simply connected by hypothesis, so the monodromy of that covering is trivial and the covering
  has a global section (`Work.SC.exists_holomorphic_modulus_of_isCoveringMap`): a single-valued
  holomorphic `Φ'` on `U` with `Φ' ≠ 0` off the pole and `‖Φ'‖ = exp (-E)` there.

The functions are then transported back to `X` (extended by `0` outside `Ω`): holomorphy is a local
statement (`holomorphicOnXAt_of_restrict_eqOn`), and at the pole the two-sided linear growth bound
`exp (-C) ‖w - z₀‖ ≤ |Φ| ≤ exp C ‖w - z₀‖`, read in the preferred chart at `x₀`, forces the zero to be
simple (`Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp`, via
`Work.Modulus.simpleZeroOfGrowth`).

Note that the `Submission.HasGreenFunctionE` interface of the parallel `Work.Modulus` development is
*unsatisfiable* (its superlevel sets `{ε ≤ E}` are required to be compact, which fails in every
punctured neighbourhood of the pole); the local arguments of that development are therefore used here
through hypotheses-only statements rather than through `HasGreenFunctionE`.

The assembly below is the assembly of `Work.SimplyConnected.ABS.exists_modulusOn` (the same theorem
with the extra hypothesis `IsConnected Ω`), with the local-branch input taken from the satisfiable
version `exists_localBranch_chartBall_of_isGreenOn`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

/-- **The holomorphic modulus of a Green function on a simply connected domain.**

Let `X` be a Riemann surface, `Ω ⊆ X` an open simply connected domain, `x₀ ∈ Ω`, and `E` a Green
function of `Ω` with pole `x₀` in the satisfiable sense of `Work.SimplyConnected.ABS.IsGreenOn`
(positive and harmonic off the pole, a bounded logarithmic pole at `x₀`, superlevel sets relatively
compact in `Ω`).  Then `E` has a holomorphic modulus on `Ω`: a function `Φ`, holomorphic at every
point of `Ω`, with a simple zero at `x₀` in the preferred chart at `x₀` and
`‖Φ x‖ = exp (-(E x))` for `x ∈ Ω`, `x ≠ x₀`.

(Anghel–Bruin–Stan, *Uniformization of Riemann surfaces revisited*, Theorem 10.) -/
theorem exists_isModulusOn_of_isGreenOn {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) (hΩsc : IsSimplyConnected Ω) {x₀ : X} (hx₀ : x₀ ∈ Ω)
    {E : X → ℝ} (hE : Work.SimplyConnected.ABS.IsGreenOn Ω x₀ E) :
    ∃ Φ : X → ℂ, Work.SimplyConnected.ABS.IsModulusOn Ω x₀ E Φ := by
  classical
  -- the domain `Ω` as an open subspace of `X`
  set U : TopologicalSpace.Opens X := ⟨Ω, hΩo⟩ with hUdef
  have hx₀U : x₀ ∈ U := hx₀
  -- `Ω` is simply connected, hence connected: no extra hypothesis is needed here
  haveI : SimplyConnectedSpace U := hΩsc
  haveI : ConnectedSpace U := inferInstance
  -- (1) local branches of the modulus on chart balls of `U`
  have hloc := Work.SimplyConnected.ABS.exists_localBranch_chartBall_of_isGreenOn
    (X := X) (U := U) hx₀U hE
  -- (2) the branch bundle over the base `U` is a covering space
  have hcov : @IsCoveringMap (Work.SC.ModulusBundle (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) U
      (Work.SC.modulusBundleTopology (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) _
      (Work.SC.branchProj (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)) :=
    Work.Modulus.isCoveringMap_branchProj_of_localBranches (z₀ := ⟨x₀, hx₀U⟩)
      (E := fun z : U => E z.1) hloc
  -- (3) the bundle is non-empty: a branch near the pole
  obtain ⟨ρ₀, Φ₀, hρ₀, hbr₀, -⟩ := hloc ⟨x₀, hx₀U⟩
  have hne : (Work.SC.branchSet (⟨x₀, hx₀U⟩ : U) (fun z : U => E z.1)).Nonempty := by
    refine ⟨(⟨x₀, hx₀U⟩, Φ₀ ⟨x₀, hx₀U⟩, Work.SC.chartDeriv Φ₀ ⟨x₀, hx₀U⟩), ?_⟩
    refine ⟨Submission.chartBall (chartAt ℂ (⟨x₀, hx₀U⟩ : U))
      ((chartAt ℂ (⟨x₀, hx₀U⟩ : U)) (⟨x₀, hx₀U⟩ : U)) ρ₀, Φ₀, hbr₀, ?_⟩
    refine ⟨?_, rfl, rfl⟩
    rw [Submission.mem_chartBall]
    exact ⟨mem_chart_source ℂ (⟨x₀, hx₀U⟩ : U), Metric.mem_ball_self hρ₀⟩
  -- (4) triviality of the monodromy over the simply connected `U`
  obtain ⟨Φ', hΦ'hol, hΦ'ne, hΦ'mod⟩ :=
    Work.SC.exists_holomorphic_modulus_of_isCoveringMap (X := U) (z₀ := ⟨x₀, hx₀U⟩)
      (E := fun z : U => E z.1) hcov hne
  -- (5) extend by `0` outside `Ω` and check the modulus conditions
  set Ψ : X → ℂ := fun x => if hx : x ∈ U then Φ' ⟨x, hx⟩ else 0 with hΨdef
  have hΨeq : ∀ (y : X) (hy : y ∈ U), Ψ y = Φ' ⟨y, hy⟩ := fun y hy => dif_pos hy
  have hholΩ : ∀ x ∈ Ω, Submission.HolomorphicOnXAt Ψ x := fun x hx =>
    holomorphicOnXAt_of_restrict_eqOn hΦ'hol hx hΨeq
  have hmodΩ : ∀ x ∈ Ω, x ≠ x₀ → ‖Ψ x‖ = Real.exp (-(E x)) := by
    intro x hx hxne
    rw [hΨeq x hx]
    exact hΦ'mod ⟨x, hx⟩ (fun h => hxne (congrArg Subtype.val h))
  refine ⟨Ψ, hholΩ, ?_, hmodΩ⟩
  -- (6) the zero at the pole is simple
  exact Work.SimplyConnected.ABS.exists_simpleZero_of_modulus_exp (Ω := Ω) hΩo hx₀ hE.2.2.2
    (hholΩ x₀ hx₀) hmodΩ

end Work.SimplyConnected.ABS
