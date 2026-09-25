import Mathlib
import Submission.NK.RamificationDeep.InertiaField
import Submission.NK.RamificationDeep.MonoDefs
import Submission.NK.RamificationDeep.algebra_isIntegral_comap
import Submission.NK.RamificationDeep.ramificationSubgroup_inf_fixingSubgroup

set_option linter.style.haveILetI false

namespace NK.RamificationDeep

/-- **The decomposition subgroup only grows when the base field shrinks.**  If `A` is stable under
all of `Gal(L/K)` then it is stable under all of `Gal(L/M)`, for any intermediate field `M`.

Indeed the two actions on `A` — that of `Gal(L/K)` and that of `Gal(L/M)` — agree under the
canonical inclusion `Gal(L/M) ↪ Gal(L/K)` (`NK.RamificationDeep.fixingIncl_smul`), so
`NK.RamificationDeep.mem_decompositionSubgroup_iff` transports membership in the decomposition
subgroup, and `A.decompositionSubgroup K = ⊤` makes the transport vacuous. -/
theorem decompositionSubgroup_restrict_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (M : IntermediateField K L)
    (hA : A.decompositionSubgroup K = ⊤) :
    A.decompositionSubgroup ↥M = ⊤ := by
  rw [eq_top_iff]
  intro ψ _
  rw [mem_decompositionSubgroup_iff A M ψ, hA]
  exact Subgroup.mem_top _

/-- **`A` is integral over `A ∩ E`**, where `E` is the inertia field of `A`.

Since `A.decompositionSubgroup K = ⊤`, the decomposition subgroup of `A` over any intermediate
field `M` is everything (`decompositionSubgroup_restrict_eq_top`); in particular this holds for
the inertia field `E`.  The Galois extension `L/K` is finite by hypothesis
(`finiteDimensional_of_isGalois`), hence so is `L/E`, and `L/E` is again Galois.  Applying
`algebra_isIntegral_comap` to the extension `L/E` gives the claim. -/
theorem algebra_isIntegral_inertiaField_comap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤) :
    Algebra.IsIntegral ↥(A.comap (algebraMap ↥(NK.RamificationDeep.inertiaField (K := K) A) L)) ↥A := by
  haveI hfd : FiniteDimensional K L := finiteDimensional_of_isGalois A hA
  haveI : FiniteDimensional ↥(NK.RamificationDeep.inertiaField (K := K) A) L := inferInstance
  haveI : IsGalois ↥(NK.RamificationDeep.inertiaField (K := K) A) L := inferInstance
  have htop : A.decompositionSubgroup ↥(NK.RamificationDeep.inertiaField (K := K) A) = ⊤ :=
    decompositionSubgroup_restrict_eq_top A (NK.RamificationDeep.inertiaField (K := K) A) hA
  exact algebra_isIntegral_comap (K := ↥(NK.RamificationDeep.inertiaField (K := K) A)) (L := L) A
    (hA := htop)

end NK.RamificationDeep
