import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic

namespace Commons.Algebra.MonoidAlgebra

/-- The `ℂ`-linear functional on the free monoid algebra over `ι` that is `1` on the
empty word and `0` on every nonempty word. -/
theorem freeAlgebra_counit (ι : Type*) :
    ∃ φ : MonoidAlgebra ℂ (FreeMonoid ι) →ₐ[ℂ] ℂ,
      ∀ v : List ι, φ (MonoidAlgebra.single (FreeMonoid.ofList v) (1 : ℂ))
        = if v = [] then 1 else 0 := by
  refine ⟨MonoidAlgebra.lift ℂ ℂ (FreeMonoid ι) (FreeMonoid.lift fun _ => (0 : ℂ)), ?_⟩
  intro v
  rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_ofList]
  induction v with
  | nil => simp
  | cons a t ih => simp

end Commons.Algebra.MonoidAlgebra