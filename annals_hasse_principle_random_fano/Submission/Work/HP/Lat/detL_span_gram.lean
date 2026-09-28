import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_basis_gram

namespace Work.HP.Lat

/-- The determinant (covolume) of the lattice spanned by a `ℤ`-linearly independent family `f` is the
square root of the Gram determinant of `f`.

Suggested route: let `L = Submodule.span ℤ (Set.range f)`.  The family `f` is a `ℤ`-basis of `L`
(independent and generating), so it suffices to compare the Gram determinant of two bases: if
`b` is another basis, then `f = b ∘ T` for a `k × k` matrix `T`, `Gram(f) = Tᵀ Gram(b) T` and both
`T` and its inverse are integral, so `|det T| = 1`, whence `det Gram(f) = det Gram(b)`.
`detL` is by definition `√(det Gram)` of the basis produced by `Submodule.basisOfPid`. -/
theorem detL_span_gram {ι : Type*} [Fintype ι] (k : ℕ) (f : Fin k → ι → ℤ)
    (hf : LinearIndependent ℤ f) :
    detL (Submodule.span ℤ (Set.range f)) =
      √(Matrix.det (Matrix.of fun i j => ∑ a, (f i a : ℝ) * (f j a : ℝ))) := by
  classical
  rw [detL_basis_gram (Submodule.span ℤ (Set.range f)) (Module.Basis.span hf)]
  simp only [Module.Basis.coe_span_apply]

end Work.HP.Lat
