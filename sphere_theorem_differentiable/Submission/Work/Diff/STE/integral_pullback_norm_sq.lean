import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The unit cube is a fundamental domain for the unit torus

`Work.Diff.STE.integral_pullback_norm_sq` transfers an integral of `‖g‖ ^ 2` over the flat
torus `UnitAddTorus ι = (ℝ/ℤ)^ι` (with the product Haar measure) to the integral of `‖g‖ ^ 2`
over the half open unit cube `(0,1]^ι`.  It is the measure-theoretic input used by the STE
development: functions on the torus are represented by their `1`-periodic representatives on
the cube.

The proof is Mathlib's `UnitAddTorus.integral_preimage` (the coordinatewise map
`t ↦ fun i => (AddCircle.equivIoc 1 0 (t i)).1` is a measure preserving equivalence
`UnitAddTorus ι ≃ᵐ (0,1]^ι`), together with the fact that on the cube the two functions agree.
The instance on `UnitAddCircle` is locally set to Mathlib's normalised Haar measure
`AddCircle.haarAddCircle` (total mass `1`), which is the measure appearing in the statement.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory

theorem integral_pullback_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℂ)
    (hg : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    ∫ t : UnitAddTorus ι, ‖g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)‖ ^ 2
        ∂(MeasureTheory.Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
      = ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ 2 := by
  -- Mathlib's torus lemmas are stated for the normalised Haar measure on `ℝ / ℤ`.
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  have hvol : MeasureTheory.Measure.pi (fun _ : ι => AddCircle.haarAddCircle)
      = (volume : Measure (UnitAddTorus ι)) := rfl
  rw [hvol]
  -- Replace the integral over the torus by the integral over the cube.
  rw [UnitAddTorus.integral_preimage (a := fun _ : ι => (0 : ℝ))]
  -- The two domains `{x | ∀ i, x i ∈ Ioc 0 (0 + 1)}` and `(0,1]^ι` coincide.
  have hset : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)}
      = Work.Diff.STE.unitCube (ι := ι) := by
    ext x
    simp [Work.Diff.STE.unitCube, Set.mem_pi]
  rw [hset]
  -- On the cube, `equivIoc 1 0` is the identity, hence the integrands agree.
  refine setIntegral_congr_fun
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)) ?_
  intro x hx
  have hx' : ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    have h1 : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] using hx
    intro i; simpa using h1 i
  have key : (fun i => (AddCircle.equivIoc (1 : ℝ) (0 : ℝ) ((x i : ℝ) : UnitAddCircle)).1)
      = x := by
    funext i
    exact congrArg Subtype.val
      (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (hx' i))
  simp only [key]

end Work.Diff.STE

end
