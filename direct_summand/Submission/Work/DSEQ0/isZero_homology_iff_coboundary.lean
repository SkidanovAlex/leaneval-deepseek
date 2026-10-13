import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs

namespace Work.DSEQ0

open CategoryTheory Limits HomologicalComplex

universe u

/-- In a cochain complex of modules indexed by `ℕ`, the homology in degree `n`
vanishes if and only if every `n`-cocycle is an `n`-coboundary, i.e. the
differential `d (n-1) n` surjects onto the kernel of `d n (n+1)`.

This is `C.ExactAt n` rewritten both through the short complex
`C.X (n-1) ⟶ C.X n ⟶ C.X (n+1)` and through the elementwise description of
exactness of short complexes of modules. -/
theorem isZero_homology_iff_coboundary (A : Type u) [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero (C.homology n) ↔
      (∀ s : ↥(C.X n), (C.d n (n + 1)).hom s = 0 →
        ∃ t : ↥(C.X (n - 1)), (C.d (n - 1) n).hom t = s) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk (n - 1) n (Nat.sub_add_cancel hn)))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk n (n + 1) rfl))]
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  exact Iff.rfl

end Work.DSEQ0
