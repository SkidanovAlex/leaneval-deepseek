import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.modulusLP_main

/-!
# The periods of the envelope's conjugate, from the vanishing of the circle-valued characters

Let `X` be a connected Riemann surface, `x₀ : X`, `U = X ∖ {x₀}` and `E` a harmonic function on `U`
(a) with a *unit* logarithmic pole at `x₀` (no positivity and no decay are used).  Write
`P := Work.ModulusLP.greenPeriodHom hEharm u₀ : π₁(U,u₀) →+ ℝ` for the period homomorphism of the
conjugate differential of `E`.

The main theorem of this file is

`periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial`:

if **every** character `π₁(X,y) →+ ℝ ⧸ 2πℤ` vanishes, then `P γ ∈ 2πℤ` for **every**
`γ ∈ π₁(U,u₀)`.

This is the sharp interface between the analysis of the holomorphic modulus and the topology of
`X`: it is the exact statement that the `Work.ModulusLP` chapter consumes
(`Work.SimplyConnected.ABS.PeriodsAreMultiplesOfTwoPi`), and it is strictly weaker than simple
connectivity of `X`.

## The argument (three inputs, all available)

1. **The periods of loops null-homotopic in `X`** are multiples of `2π`:
   `Work.ModulusLP.greenPeriodHom_two_pi_zmultiples` (decay-free form, the Sard + Stokes
   computation at the pole).  This is the *only* analytic input.
2. **The map `π₁(X ∖ {x₀}, u₀) → π₁(X, u₀)` is surjective** ("a loop can be pushed off a point"):
   `Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured`.
3. **Group theory**: by (1) the composite of `P` with the projection `ℝ → ℝ ⧸ 2πℤ` kills the kernel
   of the surjection in (2), hence descends along it (`AddMonoidHom.liftOfRightInverse`) to a
   character of `π₁(X,u₀)`, which is trivial by hypothesis.

Consequently `P` itself takes values in `2πℤ`, i.e. `exp (-(E + iE*))` is single-valued.

## Relation to the literature

Classically this is the statement that the periods of the conjugate differential of the Green
function are "2π i × integer"; the standard proof identifies the period with `2π i` times the
*local degree* of a null-homotopy at the pole, so that the periods are automatically multiples of
`2π` on the loops that are null-homotopic in `X` (input (1)) — the content of the present file is
only the passage to *all* loops of the punctured surface, which is where the topology of `X`
enters, and which needs nothing more than the vanishing of the circle-valued characters of `π₁`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The inclusion of the punctured surface `X ∖ {z₀}` in `X`, as a homomorphism of fundamental
groups at the base point `u₀`. -/
def inclMapP (z₀ : X) (u₀ : Work.Modulus.puncturedOpens z₀) :
    FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀ →* FundamentalGroup X u₀.1 :=
  FundamentalGroup.map (ContinuousMap.mk (Subtype.val : ↥(Work.Modulus.puncturedOpens z₀) → X)
    continuous_subtype_val) u₀

/-- The inclusion of the punctured surface induces a surjection on `π₁` (restated in terms of
`inclMapP`). -/
theorem surjective_inclMapP (z₀ : X) (u₀ : Work.Modulus.puncturedOpens z₀) :
    Function.Surjective (inclMapP z₀ u₀) :=
  Work.SimplyConnected.fundamentalGroup_map_surjective_of_punctured u₀

/-- **The periods of the envelope's conjugate are multiples of `2π`, from the vanishing of the
circle-valued characters of `π₁(X,·)`** (decay-free form). -/
theorem greenPeriodHom_mem_zmultiples_of_circleCharacter_trivial {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))))
    (u₀ : Work.Modulus.puncturedOpens z₀) :
    ∀ γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀,
      ∃ k : ℤ, Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ)
        = k * (2 * Real.pi) := by
  classical
  intro γ
  let Q := ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi)
  let q : ℝ →+ Q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * Real.pi))
  let φ : Additive (FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀) →+ Q :=
    { toFun := fun a => q (Work.ModulusLP.greenPeriodHom hEharm u₀ a)
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hker : (inclMapP z₀ u₀).toAdditive.ker ≤ φ.ker := by
    intro a ha
    have ha' : inclMapP z₀ u₀ (Additive.toMul a) = 1 := by
      have h1 := congrArg Additive.toMul ha
      simpa using h1
    obtain ⟨k, hk⟩ := Work.ModulusLP.greenPeriodHom_two_pi_zmultiples hEharm hpole u₀
      (Additive.toMul a) ha'
    show φ a = 0
    show q (Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul (Additive.toMul a))) = 0
    rw [hk]
    have hmem : ((k : ℝ) * (2 * Real.pi)) ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
      rw [show ((k : ℝ) * (2 * Real.pi)) = k • (2 * Real.pi) by rw [zsmul_eq_mul]]
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩
    exact QuotientAddGroup.eq_zero_iff _ |>.mpr hmem
  have hsurj : Function.Surjective (inclMapP z₀ u₀) := surjective_inclMapP z₀ u₀
  let f_inv : FundamentalGroup X u₀.1 → FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀ :=
    fun h => Classical.choose (hsurj h)
  have hf : Function.RightInverse f_inv (inclMapP z₀ u₀) :=
    fun h => Classical.choose_spec (hsurj h)
  have hfA : Function.RightInverse (fun h => Additive.ofMul (f_inv (Additive.toMul h)))
      (inclMapP z₀ u₀).toAdditive := by
    intro a
    show Additive.ofMul (inclMapP z₀ u₀ (f_inv (Additive.toMul a))) = a
    rw [hf (Additive.toMul a)]
    rfl
  set Ψ : Additive (FundamentalGroup X u₀.1) →+ Q :=
    (AddMonoidHom.liftOfRightInverse (inclMapP z₀ u₀).toAdditive
      (fun h => Additive.ofMul (f_inv (Additive.toMul h))) hfA) ⟨φ, hker⟩ with hΨdef
  have hΨ : Ψ = 0 := Subsingleton.elim _ _
  have hφ0 : φ = 0 := by
    refine AddMonoidHom.ext (fun a => ?_)
    have hcomp := AddMonoidHom.liftOfRightInverse_comp_apply (inclMapP z₀ u₀).toAdditive
      (fun h => Additive.ofMul (f_inv (Additive.toMul h))) hfA ⟨φ, hker⟩ a
    show φ a = 0
    rw [← hcomp, ← hΨdef, hΨ]
    rfl
  have h1 : φ (Additive.ofMul γ) = 0 := by rw [hφ0]; rfl
  have h2 : q (Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ)) = 0 := h1
  rw [show (0 : Q) = q 0 by simp] at h2
  have h3 : Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ)
      ∈ AddSubgroup.zmultiples (2 * Real.pi) := QuotientAddGroup.eq_zero_iff _ |>.mp h2
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h3
  exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩

/-- **The period condition for the envelope, from the vanishing of circle-valued characters.**
Stated in the unfolded form of `Work.SimplyConnected.ABS.PeriodsAreMultiplesOfTwoPi` (which lives in
`period_interface.lean` and hence cannot be imported here, since that module consumes this one). -/
theorem periodsAreMultiplesOfTwoPi_of_circleCharacter_trivial {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (hsub : ∀ y : X, Subsingleton (Additive (FundamentalGroup X y) →+
      (ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi)))) :
    ∀ (u₀ : Work.Modulus.puncturedOpens z₀)
      (γ : FundamentalGroup ↥(Work.Modulus.puncturedOpens z₀) u₀),
      ∃ k : ℤ, Work.ModulusLP.greenPeriodHom hEharm u₀ (Additive.ofMul γ)
        = k * (2 * Real.pi) :=
  fun u₀ γ =>
    greenPeriodHom_mem_zmultiples_of_circleCharacter_trivial hEharm hpole hsub u₀ γ

end Work.SimplyConnected.ABS
