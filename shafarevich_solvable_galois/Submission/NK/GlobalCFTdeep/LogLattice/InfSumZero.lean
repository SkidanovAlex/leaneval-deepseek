import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "purely infinite" sum-zero subspace of `↥T → ℝ`

For a number field `L` and a finite set of places `T` containing all infinite places, we single out
the subspace of `↥T → ℝ` consisting of the vectors which vanish at every *finite* place of `T` and
whose coordinates sum to zero.  By Dirichlet's unit theorem (in the lattice form proved by
Mathlib) this is exactly the `ℝ`-span of the log vectors of the global units, embedded into the
`T`-units; it is one of the two ingredients of Milne's `S`-unit statement
(`NK.GlobalCFTdeep.LogLattice.span_logVecLin_oneVec`), the other being the finite places.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.LogLattice

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The subspace of `↥T → ℝ` of vectors vanishing at all the finite places lying in `T` and whose
coordinates sum to zero.  Equivalently (when `T` contains all infinite places) the vector space of
those vectors which are supported on the infinite places and have coordinate sum zero. -/
def infSumZero (T : Set (Place L)) [Fintype ↥T] : Submodule ℝ (↥T → ℝ) where
  carrier := {v | (∀ q : NK.GlobalCFTdeep.SSet T, v ⟨Place.ofFinite q.1, q.2⟩ = 0) ∧
    ∑ w : ↥T, v w = 0}
  zero_mem' := by
    refine ⟨fun q => rfl, ?_⟩
    simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun q => ?_, ?_⟩
    · simp only [Pi.add_apply, hf1 q, hg1 q, add_zero]
    · rw [show (∑ w : ↥T, (f + g) w) = ∑ w : ↥T, f w + ∑ w : ↥T, g w from
        Finset.sum_add_distrib, hf2, hg2, add_zero]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun q => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf1 q, mul_zero]
    · rw [show (∑ w : ↥T, (c • f) w) = c * ∑ w : ↥T, f w from ?_, hf2, mul_zero]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Finset.mul_sum _ _ _).symm

@[simp] theorem mem_infSumZero {T : Set (Place L)} [Fintype ↥T] {v : ↥T → ℝ} :
    v ∈ infSumZero (L := L) T ↔
      (∀ q : NK.GlobalCFTdeep.SSet T, v ⟨Place.ofFinite q.1, q.2⟩ = 0) ∧
        ∑ w : ↥T, v w = 0 := Iff.rfl

/-- The purely infinite sum-zero subspace is contained in the full sum-zero hyperplane. -/
theorem infSumZero_le_sumZero {T : Set (Place L)} [Fintype ↥T] :
    infSumZero (L := L) T ≤ NK.GlobalCFTdeep.sumZero (L := L) T :=
  fun _ hv => hv.2

end NK.GlobalCFTdeep.LogLattice
