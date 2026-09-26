import Mathlib
import Submission.Work.Modular.Lattice

/-!
# Setup for Poisson summation

Definitions: the standard integer lattice `ℤ^ι ⊆ (ι → ℝ)`, integer vectors, the projection
to the torus `UnitAddTorus ι`, and the unit cube.
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard lattice `ℤ^ι` inside `ι → ℝ`. -/
def stdLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

/-- The vector of reals associated to an integer vector. -/
def intVec (m : ι → ℤ) : ι → ℝ := fun i => m i

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma intVec_apply (m : ι → ℤ) (i : ι) : intVec m i = (m i : ℝ) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma intVec_zero : intVec (0 : ι → ℤ) = 0 := by
  ext i; simp [intVec]

omit [Fintype ι] [DecidableEq ι] in
lemma intVec_add (m m' : ι → ℤ) : intVec (m + m') = intVec m + intVec m' := by
  ext i; simp [intVec]

/-- The canonical projection `ι → ℝ → UnitAddTorus ι`. -/
def projTorus : (ι → ℝ) → UnitAddTorus ι := fun x i => (x i : UnitAddCircle)

omit [DecidableEq ι] in
@[simp] lemma projTorus_apply (x : ι → ℝ) (i : ι) : projTorus x i = (x i : UnitAddCircle) := rfl

lemma projTorus_add_intVec (x : ι → ℝ) (m : ι → ℤ) :
    projTorus (x + intVec m) = projTorus x := by
  funext i
  simp [projTorus, intVec]

/-- The half-open unit cube `(0,1]^ι`. -/
def unitCube : Set (ι → ℝ) := Set.pi Set.univ fun _ => Set.Ioc (0:ℝ) 1

omit [DecidableEq ι] in
lemma measurableSet_unitCube : MeasurableSet (unitCube (ι := ι)) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioc

omit [DecidableEq ι] in
lemma volume_unitCube : volume (unitCube (ι := ι)) = 1 := by
  rw [unitCube, Real.volume_pi_Ioc]
  simp

end Work.Modular

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An integer vector, as an element of `EuclideanSpace ℝ ι`. -/
def intVecE (m : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (intVec m)

@[simp] lemma intVecE_apply (m : ι → ℤ) (i : ι) : intVecE m i = (m i : ℝ) := rfl

@[simp] lemma intVecE_zero : intVecE (0 : ι → ℤ) = 0 := by
  ext i; simp [intVecE]

lemma intVecE_add (m m' : ι → ℤ) : intVecE (m + m') = intVecE m + intVecE m' := by
  ext i; simp [intVecE, intVec]

/-- The "integer lattice" in `EuclideanSpace ℝ ι`: vectors all of whose coordinates are
integers. -/
def intLatticeE (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℤ (EuclideanSpace ℝ ι) :=
  ZLattice.comap ℝ (stdLattice ι) (EuclideanSpace.equiv ι ℝ).toLinearMap

/-- The unit cube `(0,1]^ι` in `EuclideanSpace ℝ ι`. -/
def cubeE (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  (EuclideanSpace.equiv ι ℝ) ⁻¹' unitCube

lemma mem_intLatticeE_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) :
    x ∈ intLatticeE ι ↔ EuclideanSpace.equiv ι ℝ x ∈ stdLattice ι := by
  simp only [intLatticeE, ZLattice.comap, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  rfl

end Work.Modular

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_stdLattice {x : ι → ℝ} :
    x ∈ stdLattice ι ↔ ∀ i, ∃ m : ℤ, x i = (m : ℝ) := by
  rw [stdLattice, Submodule.mem_span_range_iff_exists_fun ℤ]
  constructor
  · rintro ⟨c, hc⟩ i
    refine ⟨c i, ?_⟩
    rw [← hc]
    simp [Pi.basisFun, Finset.sum_apply, Pi.single_apply]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    ext i
    simp [Pi.basisFun, Finset.sum_apply, Pi.single_apply, hc i]

lemma intVec_mem_stdLattice (m : ι → ℤ) : intVec m ∈ stdLattice ι :=
  mem_stdLattice.mpr fun i => ⟨m i, rfl⟩

lemma mem_intLatticeE {x : EuclideanSpace ℝ ι} :
    x ∈ intLatticeE ι ↔ ∀ i, ∃ m : ℤ, x i = (m : ℝ) := by
  rw [intLatticeE, ZLattice.comap, Submodule.mem_comap, mem_stdLattice]
  rfl

end Work.Modular
