import Mathlib.GroupTheory.Nilpotent
import Mathlib.FieldTheory.Galois.Basic
import Submission.Work.GenericKernelReduction.Nilpotent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- The generic-kernel hypothesis implies its closure form: a proper solution of an embedding
problem over `ℚ` can be realised inside the fixed algebraic closure `AlgebraicClosure ℚ`
(`Work.GenericKernelReduction.inClosure_of_splitEmbeddingSolvable`). -/
theorem genericKernelSolvableInClosure_of_genericKernel (h : GenericKernelSolvable) :
    GenericKernelSolvableInClosure :=
  fun L _ _ p _ n ν ρ Φ hdesc => inClosure_of_splitEmbeddingSolvable (h L p n ν ρ Φ hdesc)

/-- The closure form of the hypothesis implies the primary form (forget that the solution lies in
`AlgebraicClosure ℚ`), so the two forms of `Work.GenericKernelReduction.GenericKernelSolvable`
are equivalent. -/
theorem genericKernelSolvable_of_inClosure (h : GenericKernelSolvableInClosure) :
    GenericKernelSolvable :=
  fun L _ _ p _ n ν ρ Φ hdesc => splitEmbeddingSolvable_of_inClosure (h L p n ν ρ Φ hdesc)

/-- **Reduction of Theorem 14 of Schmidt–Wingberg (over `ℚ`) to the generic-kernel
hypothesis.**  If for every finite Galois `L/ℚ`, every prime `p`, all `n, ν` and every action of
`Gal(L/ℚ)` on `F^(n) = FreeGroup (Fin n)` whose descent to `F^(n)/F^(n)(ν)` is `Φ`, the split
embedding problem with kernel `F^(n)/F^(n)(ν)` and quotient `Gal(L/ℚ)` has a proper solution,
then every split embedding problem over `ℚ` with finite nilpotent kernel has a proper solution. -/
theorem splitEmbeddingTheoremOverRat_of_genericKernel (h : GenericKernelSolvable) :
    Submission.SplitEmbeddingTheoremOverRat := by
  intro L _ _ N _ _ hN φ
  exact splitEmbeddingSolvable_of_inClosure
    (splitEmbeddingSolvedInClosure_of_genericKernel_nilpotent
      (genericKernelSolvableInClosure_of_genericKernel h) L N hN φ)

/-- **Shafarevich's theorem from the generic-kernel hypothesis**: every finite solvable group is
the Galois group of a finite Galois extension of `ℚ`.  This is Ore's reduction
(`Submission.realizable_of_solvable_of_split`) applied to
`splitEmbeddingTheoremOverRat_of_genericKernel`. -/
theorem realizable_of_genericKernel (h : GenericKernelSolvable) :
    ∀ (G : Type) [Group G] [Finite G] [Group.IsSolvable G], Submission.RealizableOver ℚ G :=
  Submission.realizable_of_solvable_of_split (splitEmbeddingTheoremOverRat_of_genericKernel h)

/-- The generic-kernel hypothesis implies the single deep input of the development,
`Submission.MinimalNormalKernelStep`. -/
theorem minimalNormalKernelStep_of_genericKernel (h : GenericKernelSolvable) :
    Submission.MinimalNormalKernelStep.{0} :=
  Submission.minimalNormalKernelStep_of_split (splitEmbeddingTheoremOverRat_of_genericKernel h)

end Work.GenericKernelReduction
