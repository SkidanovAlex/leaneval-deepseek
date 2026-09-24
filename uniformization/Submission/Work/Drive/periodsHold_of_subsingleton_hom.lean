import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.exists_intHom_greenPeriodHom_ker

/-!
Guidance from the project lead (the requester):

# Area A — conjugate periods are in 2πℤ, from Hom(π₁X, ℝ) = 0 (no simple connectivity)

`Work.Drive.PeriodsHold X` — every harmonic `E` on `X∖{z₀}` with a unit logarithmic pole at `z₀`
has all its conjugate periods in `2πℤ` — follows from `¬ CompactSpace X` and
`Hom(π₁(X,x), ℝ) = 0`.

## How the present file is organised

The two ingredients are

* **the integrality of the periods of the loops that are null-homotopic in `X`**, together with the
  *sharpening* that the relevant integers are the values of a single integer-valued homomorphism
  `W` of `π₁(X∖{z₀})` (`Work.Drive.exists_intHom_greenPeriodHom_ker`, in the module
  `Submission.Work.Drive.periodWindingExtension`; its docstring records the two routes: the global
  phase `Θ` of `Work.Drive.exists_continuous_singleZero_phase` plus the branch-bundle argument, and
  the torsion-of-the-obstruction argument);
* **the group theory of the descent**, carried out here: `P − 2π·W` kills `ker j`, hence descends
  along the surjection `j : π₁(X∖{z₀}) ↠ π₁(X)` to a homomorphism `π₁(X) →+ ℝ`, which vanishes by
  the challenge hypothesis; consequently `P = 2π·W` on *all* of `π₁(X∖{z₀})`, i.e. the periods of
  `P` are multiples of `2π`.

The elementary group theory (notably the base-point transport of the hypothesis) is proved in this
file.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Base-point transport of the vanishing of real characters.**  Conjugation along a path
identifies the fundamental groups at two base points, hence the corresponding character groups. -/
theorem subsingleton_addHom_real_of_path {x y : X} (γ : Path x y)
    (h : Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)) :
    Subsingleton (Additive (FundamentalGroup X y) →+ ℝ) := by
  have e : Additive (FundamentalGroup X x) ≃+ Additive (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toAdditive
  refine ⟨fun f g => ?_⟩
  have h' : f.comp e.toAddMonoidHom = g.comp e.toAddMonoidHom := Subsingleton.elim _ _
  refine AddMonoidHom.ext (fun z => ?_)
  obtain ⟨a, rfl⟩ := e.surjective z
  exact congrFun (congrArg DFunLike.coe h') a

/-- **The periods from the integer-valued extension.**  If the periods of the loops of `X ∖ {z₀}`
that are null-homotopic in `X` are the values of an integer-valued homomorphism `W` of
`π₁(X∖{z₀},u₀)` (times `2π`), and `π₁(X,u₀.1)` has no non-trivial character to `ℝ`, then *every*
period is a multiple of `2π`.

Proof: the homomorphism `μ := P − 2π·W` kills `ker j`, hence factors through the surjection
`j : π₁(X∖{z₀},u₀) ↠ π₁(X,u₀.1)` (`AddMonoidHom.liftOfRightInverse`); the resulting real character
of `π₁(X,u₀.1)` vanishes by hypothesis, so `μ = 0` and `P γ = (W γ)·2π`. -/
theorem greenPeriodHom_mem_zmultiples_of_intHom_extension (hX : ¬ CompactSpace X)
    {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    [Subsingleton (Additive (FundamentalGroup X u₀.1) →+ ℝ)] :
    ∀ γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀,
      ∃ k : ℤ, Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ) = k * (2 * Real.pi) := by
  classical
  obtain ⟨W, hW⟩ := exists_intHom_greenPeriodHom_ker hX hEharm hpole u₀
  let P : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℝ :=
    Work.ModulusLP.greenPeriodHom hEharm u₀
  let μ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℝ :=
    { toFun := fun a => P a - (W a : ℝ) * (2 * Real.pi)
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, Int.cast_add]; ring }
  have hker : (Work.SimplyConnected.ABS.inclMapP z₀ u₀).toAdditive.ker ≤ μ.ker := by
    intro a ha
    have ha1 : Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul a) = 1 := by
      have h1 := congrArg Additive.toMul ha
      simpa using h1
    have h2 : P a = (W a : ℝ) * (2 * Real.pi) := hW a ha1
    show μ a = 0
    change P a - (W a : ℝ) * (2 * Real.pi) = 0
    rw [h2]; ring
  -- the descent along the surjection
  let j : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+
      Additive (FundamentalGroup X u₀.1) := (Work.SimplyConnected.ABS.inclMapP z₀ u₀).toAdditive
  have hsurj : Function.Surjective j :=
    Work.SimplyConnected.ABS.surjective_inclMapP z₀ u₀
  let f_inv : Additive (FundamentalGroup X u₀.1) →
      Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) :=
    fun h => Classical.choose (hsurj h)
  have hf : Function.RightInverse f_inv j := fun h => Classical.choose_spec (hsurj h)
  let q : Additive (FundamentalGroup X u₀.1) →+ ℝ :=
    (AddMonoidHom.liftOfRightInverse j f_inv hf) ⟨μ, hker⟩
  have hq0 : q = 0 := Subsingleton.elim _ _
  have hμ0 : μ = 0 := by
    have hcomp : q.comp j = μ := AddMonoidHom.liftOfRightInverse_comp j f_inv hf ⟨μ, hker⟩
    rw [← hcomp, hq0, AddMonoidHom.zero_comp]
  intro γ
  have h1 : μ (Additive.ofMul γ) = 0 := by rw [hμ0]; rfl
  refine ⟨W (Additive.ofMul γ), ?_⟩
  have h2 : P (Additive.ofMul γ) - (W (Additive.ofMul γ) : ℝ) * (2 * Real.pi) = 0 := h1
  have h3 : P (Additive.ofMul γ) = (W (Additive.ofMul γ) : ℝ) * (2 * Real.pi) := by linarith
  show Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ)
      = (W (Additive.ofMul γ)) * (2 * Real.pi)
  exact h3

/-- **Area A: `PeriodsHold X` from `¬ CompactSpace X` and the vanishing of the real characters of
`π₁(X,·)`.** -/
theorem periodsHold_of_subsingleton_hom {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    Work.Drive.PeriodsHold X := by
  haveI : PathConnectedSpace X := by
    haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  intro z₀ E hEharm hpole u₀ γ
  haveI : Subsingleton (Additive (FundamentalGroup X u₀.1) →+ ℝ) :=
    subsingleton_addHom_real_of_path (PathConnectedSpace.somePath x u₀.1) (by infer_instance)
  exact greenPeriodHom_mem_zmultiples_of_intHom_extension hX hEharm hpole u₀ γ

end Work.Drive
