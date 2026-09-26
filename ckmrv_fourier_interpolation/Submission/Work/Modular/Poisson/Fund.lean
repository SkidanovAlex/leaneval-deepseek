import Mathlib
import Submission.Work.Modular.Poisson.Std
import Submission.Work.Poisson.covolume_intLatticeE

/-!
# The unit cube as a fundamental domain

We show that the half-open cube `(0,1]^ι` is a fundamental domain for the standard lattice
`ℤ^ι ⊆ (ι → ℝ)`, and transport this to `EuclideanSpace ℝ ι` and to an arbitrary lattice
`L ⊆ EuclideanSpace ℝ ι` related to `ℤ^ι` by a linear equivalence `d`.
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unique lattice element `g` with `g + x ∈ (0,1]^ι`. -/
def cubeShift (x : ι → ℝ) : ↥(stdLattice ι) :=
  ⟨fun i => (⌊1 - x i⌋ : ℝ), mem_stdLattice.mpr fun i => ⟨⌊1 - x i⌋, rfl⟩⟩

lemma vadd_cubeShift (x : ι → ℝ) (i : ι) :
    (cubeShift x +ᵥ x) i = (⌊1 - x i⌋ : ℝ) + x i := by
  rw [Submodule.vadd_def, vadd_eq_add, Pi.add_apply]
  rfl

lemma cubeShift_add_mem (x : ι → ℝ) : cubeShift x +ᵥ x ∈ unitCube (ι := ι) := by
  rw [unitCube, Set.mem_univ_pi]
  intro i
  rw [vadd_cubeShift]
  have h1 := Int.lt_floor_add_one (1 - x i)
  have h2 := Int.floor_le (1 - x i)
  simp only [Set.mem_Ioc]
  constructor <;> linarith

lemma cubeShift_unique (x : ι → ℝ) {g : ↥(stdLattice ι)}
    (hg : g +ᵥ x ∈ unitCube (ι := ι)) : g = cubeShift x := by
  obtain ⟨m, hm⟩ : ∃ m : ι → ℤ, (g : ι → ℝ) = intVec m := by
    have h := mem_stdLattice.mp g.2
    choose m hm using h
    exact ⟨m, funext fun i => hm i⟩
  rw [unitCube, Set.mem_univ_pi] at hg
  have hgi : ∀ i, (g : ι → ℝ) i = (m i : ℝ) := fun i => by rw [hm]; rfl
  have key : ∀ i, (m i : ℤ) = ⌊1 - x i⌋ := fun i => by
    have h1 : (g : ι → ℝ) i + x i ≤ 1 := (hg i).2
    have h2 : 0 < (g : ι → ℝ) i + x i := (hg i).1
    rw [hgi i] at h1 h2
    rw [eq_comm, Int.floor_eq_iff]
    constructor <;> linarith
  ext i
  show (g : ι → ℝ) i = (cubeShift x : ι → ℝ) i
  rw [hgi i, key i]
  rfl

@[simp] lemma vadd_mem_unitCube_iff (g : ↥(stdLattice ι)) (x : ι → ℝ) :
    g +ᵥ x ∈ unitCube (ι := ι) ↔ g = cubeShift x :=
  ⟨fun h => cubeShift_unique x h, fun h => h ▸ cubeShift_add_mem x⟩

/-- The half-open cube `(0,1]^ι` is a fundamental domain for the standard lattice. -/
theorem isAddFundamentalDomain_unitCube :
    IsAddFundamentalDomain (stdLattice ι) (unitCube (ι := ι)) volume :=
  IsAddFundamentalDomain.mk' measurableSet_unitCube.nullMeasurableSet
    (fun x => ⟨cubeShift x, cubeShift_add_mem x, fun g hg => cubeShift_unique x hg⟩)

/-- The canonical bijection `ℤ^ι ≃ ℤ^ι ⊆ EuclideanSpace ℝ ι`. -/
def stdEquivIntLattice (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ↥(stdLattice ι) ≃ ↥(intLatticeE ι) where
  toFun g := ⟨(EuclideanSpace.equiv ι ℝ).symm (g : ι → ℝ), by
    rw [mem_intLatticeE]
    simpa using mem_stdLattice.mp g.2⟩
  invFun h := ⟨(EuclideanSpace.equiv ι ℝ) (h : EuclideanSpace ℝ ι), by
    rw [mem_stdLattice]
    simpa using mem_intLatticeE.mp h.2⟩
  left_inv g := by ext; simp
  right_inv h := by ext; simp

/-- The unit cube in `EuclideanSpace ℝ ι` is a fundamental domain for the integer lattice. -/
theorem isAddFundamentalDomain_intLatticeE :
    IsAddFundamentalDomain (intLatticeE ι) (cubeE ι) volume := by
  have h := isAddFundamentalDomain_unitCube (ι := ι)
  have h' := h.preimage_of_equiv (f := EuclideanSpace.equiv ι ℝ)
    (Work.Poisson.measurePreserving_euclideanSpaceEquiv ι).quasiMeasurePreserving
    (e := fun g : ↥(stdLattice ι) => stdEquivIntLattice ι g)
    (stdEquivIntLattice ι).bijective ?_
  · exact h'
  · intro g x
    simp only [Submodule.vadd_def, vadd_eq_add, map_add]
    congr 1

/-- The unit cube in `EuclideanSpace ℝ ι` has volume one. -/
theorem volume_cubeE : volume (cubeE (ι := ι)) = 1 := by
  show volume ((EuclideanSpace.equiv ι ℝ) ⁻¹' unitCube (ι := ι)) = 1
  rw [← Measure.map_apply (EuclideanSpace.equiv ι ℝ).continuous.measurable measurableSet_unitCube,
    (Work.Poisson.measurePreserving_euclideanSpaceEquiv ι).map_eq, volume_unitCube]

variable (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L]
variable (d : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι)

/-- The bijection `ℤ^ι ≃ L` induced by a linear equivalence `d` with `d '' L = ℤ^ι`. -/
def intLatticeEquivL (hd : ∀ x : EuclideanSpace ℝ ι, x ∈ L ↔ d x ∈ intLatticeE ι) :
    ↥(intLatticeE ι) ≃ ↥L where
  toFun w := ⟨d.symm (w : EuclideanSpace ℝ ι), (hd _).mpr (by simp)⟩
  invFun z := ⟨d (z : EuclideanSpace ℝ ι), (hd _).mp z.2⟩
  left_inv w := by ext; simp
  right_inv z := by ext; simp

/-- The preimage under `d` of the unit cube is a fundamental domain for `L`. -/
theorem isAddFundamentalDomain_preimage
    (hd : ∀ x : EuclideanSpace ℝ ι, x ∈ L ↔ d x ∈ intLatticeE ι) :
    IsAddFundamentalDomain L (d ⁻¹' cubeE ι) volume := by
  have h := isAddFundamentalDomain_intLatticeE (ι := ι)
  have hdet : LinearMap.det (d : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 := by
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  refine h.preimage_of_equiv (f := (d : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι))
    (Measure.LinearMap.quasiMeasurePreserving volume
      (d : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) hdet)
    (e := fun w : ↥(intLatticeE ι) => intLatticeEquivL L d hd w)
    (intLatticeEquivL L d hd).bijective ?_
  intro w x
  simp only [Submodule.vadd_def, vadd_eq_add, map_add]
  congr 1
  exact LinearEquiv.apply_symm_apply d (w : EuclideanSpace ℝ ι)

end Work.Modular
