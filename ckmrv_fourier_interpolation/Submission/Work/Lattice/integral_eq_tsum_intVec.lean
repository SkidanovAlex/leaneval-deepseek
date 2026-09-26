import Mathlib
import Submission.Work.Lattice.poissonBasics

namespace Work.Lattice

open MeasureTheory Set
open scoped Pointwise

/-- The vector `v ∈ ℤⁿ` viewed as an element of the lattice `ℤⁿ ⊆ ℝⁿ`. -/
theorem intVecToReal_mem {n : ℕ} (v : Fin n → ℤ) : intVecToReal v ∈ intVec n := by
  rw [mem_intVec]
  exact fun i => ⟨v i, rfl⟩

/-- The canonical bijection between `ℤⁿ` and the lattice `ℤⁿ ⊆ ℝⁿ`. -/
noncomputable def intVecEquiv (n : ℕ) : (Fin n → ℤ) ≃ intVec n where
  toFun v := ⟨intVecToReal v, intVecToReal_mem v⟩
  invFun w := fun i => Classical.choose (mem_intVec.mp w.2 i)
  left_inv v := by
    funext i
    exact (Int.cast_injective (Classical.choose_spec (mem_intVec.mp (intVecToReal_mem v) i))).symm
  right_inv w := by
    refine Subtype.ext (funext fun i => ?_)
    exact (Classical.choose_spec (mem_intVec.mp w.2 i)).symm

@[simp] theorem intVecEquiv_coe {n : ℕ} (v : Fin n → ℤ) :
    ((intVecEquiv n v : intVec n) : Fin n → ℝ) = intVecToReal v := rfl

/-- The additive action of the lattice element attached to `v` is translation by `v`. -/
theorem intVecEquiv_vadd {n : ℕ} (v : Fin n → ℤ) (x : Fin n → ℝ) :
    (intVecEquiv n v) +ᵥ x = x + intVecToReal v := by
  show intVecToReal v + x = x + intVecToReal v
  exact add_comm _ _

instance instCountableIntVec (n : ℕ) : Countable (intVec n) :=
  (intVecEquiv n).symm.injective.countable

/-- Integration over `ℝⁿ` can be replaced by summing the integrals over the translates of the
unit cube `(0,1]ⁿ` by integer vectors, i.e. the unit cube is a fundamental domain for `ℤⁿ`. -/
theorem integral_eq_tsum_intVec {n : ℕ} (g : (Fin n → ℝ) → ℂ) (hg : MeasureTheory.Integrable g) :
    ∫ y, g y = ∑' v : Fin n → ℤ,
      ∫ x in Work.Lattice.unitCube n, g (x + Work.Lattice.intVecToReal v) := by
  have hfd : IsAddFundamentalDomain (intVec n) (unitCube n)
      (volume : Measure (Fin n → ℝ)) := isAddFundamentalDomain_unitCube n
  calc ∫ y, g y
      = ∑' w : intVec n, ∫ x in unitCube n, g (w +ᵥ x) := hfd.integral_eq_tsum'' g hg
    _ = ∑' v : Fin n → ℤ, ∫ x in unitCube n, g (intVecEquiv n v +ᵥ x) :=
        (Equiv.tsum_eq (intVecEquiv n) fun w => ∫ x in unitCube n, g (w +ᵥ x)).symm
    _ = ∑' v : Fin n → ℤ, ∫ x in Work.Lattice.unitCube n,
          g (x + Work.Lattice.intVecToReal v) :=
        tsum_congr fun v => by simp only [intVecEquiv_vadd]

end Work.Lattice
