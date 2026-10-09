import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

/-- **A valuation subring of a Galois extension is determined by its restrictions to the finite
normal intermediate fields.**

Let `K' / K` be a Galois extension and `A`, `B` valuation subrings of `K'`.  If `A` and `B` have
the same trace `A.comap (algebraMap ↥L K') = B.comap (algebraMap ↥L K')` on every
finite-dimensional normal intermediate field `L`, then `A = B`.

Indeed, any `x : K'` lies in a finite Galois (in particular finite normal) intermediate field `L`
by `Commons.FieldTheory.Galois.exists_finite_galois_containing`; comparing the two traces at the
element `x ∈ L` yields `x ∈ A ↔ x ∈ B`. -/
theorem eq_of_comap_eq_forall_finite_normal {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    [IsGalois K K'] (A B : ValuationSubring K')
    (h : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L],
      A.comap (algebraMap ↥L K') = B.comap (algebraMap ↥L K')) : A = B := by
  apply ValuationSubring.ext
  intro x
  obtain ⟨L, hfin, hgal, hxL⟩ := exists_finite_galois_containing (k := K) (K := K') x
  haveI : FiniteDimensional K L := hfin
  haveI : Normal K L := hgal.to_normal
  have hL := h L
  have key : (⟨x, hxL⟩ : L) ∈ A.comap (algebraMap ↥L K') ↔
      (⟨x, hxL⟩ : L) ∈ B.comap (algebraMap ↥L K') := by rw [hL]
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at key
  simpa using key

end Commons.FieldTheory.Galois