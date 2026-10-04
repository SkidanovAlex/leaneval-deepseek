import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.cube_fubini

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pulling back `L²` functions from the unit cube to the unit torus

The half open unit cube `unitCube = (0,1]^ι` is a fundamental domain for the unit torus
`UnitAddTorus ι = (ℝ/ℤ)^ι`, and the coordinatewise `Ioc`-representative

`rep : UnitAddTorus ι → (ι → ℝ)`, `rep t = fun i => (AddCircle.equivIoc 1 0 (t i)).1`

identifies the torus (with its Haar probability measure `Measure.pi (fun _ => haarAddCircle)`)
with the cube (with Lebesgue measure restricted to the cube), up to a null set.

The main theorem `memLp_comp_rep` is the `L²` consequence: the pullback `g ∘ rep` of a square
integrable function `g` on the cube is square integrable on the torus.

The mathematical content is the measure preservation statement `measurePreserving_rep`: the
coordinatewise representative map pushes the product Haar measure onto Lebesgue measure
restricted to the cube.  It is obtained from Mathlib's one dimensional fact
`AddCircle.measurePreserving_equivIoc` (Haar measure on `AddCircle 1` pushes forward, via
`equivIoc`, to Lebesgue measure on `(0,1]`), the measure preserving product construction
`measurePreserving_pi`, and the identification of Lebesgue measure restricted to the cube with
the product of the restricted one dimensional measures (`restrict_unitCube_measure`).
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard volume on the unit additive circle is its Haar probability measure. -/
lemma volume_unitAddCircle_eq_haarAddCircle :
    (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The `Ioc`-representative map `AddCircle 1 → (0,1]` pushes the Haar measure of the unit
circle onto Lebesgue measure restricted to `(0,1]`. -/
lemma measurePreserving_equivIoc_haar :
    MeasurePreserving (fun a : AddCircle (1 : ℝ) => (AddCircle.equivIoc 1 0 a).1)
      AddCircle.haarAddCircle
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
  -- `Subtype.val : (0,1] → ℝ` pushes `Measure.comap Subtype.val volume` to `volume.restrict (0,1]`
  have hsub : MeasurePreserving (Subtype.val : Set.Ioc (0 : ℝ) (0 + 1) → ℝ)
      (Measure.comap Subtype.val (volume : Measure ℝ))
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (0 + 1))) :=
    ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Ioc volume⟩
  have h := hsub.comp (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
  rw [volume_unitAddCircle_eq_haarAddCircle] at h
  simpa only [zero_add, Function.comp_def] using h

omit [DecidableEq ι] in
/-- The product of the restricted one dimensional Lebesgue measures is Lebesgue measure
restricted to the unit cube. -/
lemma pi_restrict_Ioc_eq_restrict_unitCube :
    (Measure.pi (fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)))
      = (volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι)) :=
  restrict_unitCube_measure.symm

omit [DecidableEq ι] in
/-- **The `Ioc`-representative map is measure preserving.** The coordinatewise
`Ioc`-representative of the unit torus pushes the product Haar measure onto Lebesgue measure
restricted to the unit cube. -/
lemma measurePreserving_rep :
    MeasurePreserving (fun t : UnitAddTorus ι => fun i => (AddCircle.equivIoc 1 0 (t i)).1)
      (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
      ((volume : Measure (ι → ℝ)).restrict (unitCube (ι := ι))) := by
  have h := measurePreserving_pi (fun _ : ι => AddCircle.haarAddCircle)
      (fun _ : ι => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
      (fun _ => measurePreserving_equivIoc_haar)
  rw [← pi_restrict_Ioc_eq_restrict_unitCube]
  exact h

theorem memLp_comp_rep {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℂ}
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    MeasureTheory.MemLp (fun t : UnitAddTorus ι => g (fun i => (AddCircle.equivIoc 1 0 (t i)).1)) 2
      (MeasureTheory.Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) := by
  have hT : MeasurePreserving (fun t : UnitAddTorus ι => fun i => (AddCircle.equivIoc 1 0 (t i)).1)
      (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
      (volume.restrict (unitCube (ι := ι))) :=
    measurePreserving_rep (ι := ι)
  exact hg.comp_measurePreserving hT

end Work.Diff.STE
