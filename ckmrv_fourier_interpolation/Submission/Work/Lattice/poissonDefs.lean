import Mathlib

/-!
# Periodization over `ℤⁿ` and its lift to the torus

This file contains the basic definitions used to prove Poisson summation over `ℤⁿ`:
the unit cube `(0,1]ⁿ` (a fundamental domain of `ℤⁿ ⊆ ℝⁿ`), the lattice `ℤⁿ` as an additive
subgroup of `ℝⁿ`, the periodization `∑_{v ∈ ℤⁿ} f (x + v)` of a Schwartz function, and its
descent to the torus `(ℝ/ℤ)ⁿ`.
-/

namespace Work.Lattice

open scoped FourierTransform SchwartzMap

/-- The half-open unit cube `(0,1]ⁿ`, a fundamental domain for the lattice `ℤⁿ ⊆ ℝⁿ`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Ioc (0 : ℝ) 1

/-- The lattice `ℤⁿ` as an additive subgroup of `ℝⁿ`. -/
def intVec (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.zmultiples (1 : ℝ)

/-- The vector `(v₁,…,vₙ) ∈ ℝⁿ` attached to `v ∈ ℤⁿ`. -/
def intVecToReal {n : ℕ} (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

@[simp] theorem intVecToReal_apply {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    intVecToReal v i = (v i : ℝ) := rfl

@[simp] theorem mem_unitCube {n : ℕ} {x : Fin n → ℝ} :
    x ∈ unitCube n ↔ ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [unitCube, Set.mem_pi]
  simp

@[simp] theorem mem_intVec {n : ℕ} {y : Fin n → ℝ} :
    y ∈ intVec n ↔ ∀ i, ∃ m : ℤ, y i = (m : ℝ) := by
  rw [intVec, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, forall_true_left, AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul,
    mul_one, eq_comm]

/-- The periodization over `ℤⁿ` of a Schwartz function `f` on `ℝⁿ`. -/
noncomputable def periodization {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : Fin n → ℝ) : ℂ :=
  ∑' v : Fin n → ℤ, f (WithLp.toLp 2 (x + intVecToReal v))

/-- The representative in `(0,1]` of a point of `ℝ/ℤ`. -/
noncomputable def circleSec (t : UnitAddCircle) : ℝ := (AddCircle.equivIoc (1 : ℝ) 0 t : ℝ)

/-- The lift to the `n`-torus of the periodization of `f`. -/
noncomputable def torusLift {n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (t : UnitAddTorus (Fin n)) : ℂ :=
  periodization f fun i => circleSec (t i)

end Work.Lattice
