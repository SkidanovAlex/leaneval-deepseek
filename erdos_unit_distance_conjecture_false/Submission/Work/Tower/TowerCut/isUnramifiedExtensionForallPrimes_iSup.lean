import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup

namespace Work.Tower.TowerCut

open NumberField
open scoped Classical nonZeroDivisors

variable {ι : Type*} [Finite ι] [Nonempty ι] {F A : Type*} [Field F] [NumberField F]
  [Field A] [Algebra F A]

/-- Auxiliary induction principle for `isUnramifiedExtensionForallPrimes_iSup`: for a fixed
index `i₀`, the supremum of any finite subfamily containing `M i₀` is finite-dimensional over
`F` and unramified at all primes.  Proved by induction on the remaining indices, applying the
binary compositum result at each step. -/
theorem finiteDimensional_and_isUnramifiedExtensionForallPrimes_sup_insert
    (M : ι → IntermediateField F A) [∀ i, FiniteDimensional F (M i)]
    (h : ∀ i, Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(M i)) (i₀ : ι) :
    ∀ s : Finset ι,
      FiniteDimensional F ↥((insert i₀ s).sup M) ∧
        Work.Tower.IsUnramifiedExtensionForallPrimes F ↥((insert i₀ s).sup M) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.insert_empty, Finset.sup_singleton]
      exact ⟨inferInstance, h i₀⟩
  | insert a s _ ih =>
      rw [Finset.insert_comm i₀ a s, Finset.sup_insert]
      have : FiniteDimensional F ↥((insert i₀ s).sup M) := ih.1
      exact ⟨inferInstance,
        Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup (h a) ih.2⟩

theorem isUnramifiedExtensionForallPrimes_iSup
    (M : ι → IntermediateField F A) [∀ i, FiniteDimensional F (M i)]
    (h : ∀ i, Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(M i)) :
    Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(⨆ i, M i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [← Finset.sup_univ_eq_iSup, ← Finset.insert_erase (Finset.mem_univ i₀)]
  exact (finiteDimensional_and_isUnramifiedExtensionForallPrimes_sup_insert M h i₀
    (Finset.univ.erase i₀)).2

end Work.Tower.TowerCut
